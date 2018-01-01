#include "libavutil/parseutils.h"
#include "libavutil/avstring.h"
#include "libavutil/opt.h"
#include "libavutil/dict.h"
#include "avformat.h"
#include "avio_internal.h"
#include "url.h"

#include <stdarg.h>
#include "internal.h"
#include "network.h"
#include "os_support.h"
#include <fcntl.h>
#if HAVE_POLL_H
#include <sys/poll.h>
#endif
#if HAVE_PTHREAD_CANCEL
#include <pthread.h>
#endif

#define HOST_IP	"192.168.1.200"
#define MAX_CLIENT_NUM 128

#define FCC_BUF_SIZE (8*1024*1024)
#define ONCE_SIZE (5000*188)

#define TCP_RECV_BUF_SIZE 1024
#define TCP_SEND_BUF_SIZE (1024)

#define FCCVERSION 0
#define FccSubcMsgDataLen 1308  //sub massage data length: 8 bytes

#define NAL_TYPE_UNKNOW		0x0
#define NAL_TYPE_NON_IDR 	0x1
#define NAL_TYPE_IDR		0x2
#define NAL_TYPE_SPS		0x4
#define NAL_TYPE_PPS		0x8

typedef enum EFccMsgType
{
	EFccMsgType_Requery = 0,
	EFccMsgType_Response,
	EFccMsgType_Request,
	EFccMsgType_Send
}EFccMsgType;

typedef enum EFccSubcMsgType
{
	EFccSubMsgType_Status = 0,
	EFccSubMsgType_FstPts,
	EFccSubMsgType_LstPts,
	EFccSubMsgType_DatLen,
	EFccSubMsgType_MaxInt,
	EFccSubMsgType_MinInt,
	EFccSubMsgType_AvgInt
}EFccSubcMsgType;

typedef enum EFccStatus
{
	EFccStatus_NotAvailable = 0,
	EFccStatus_Available
}EFccStatus;

typedef struct ClientContext {
	URLContext *uc_tcp_client;
	pthread_t tid;
	unsigned char *client_buf;
	int client_buf_data_len;
	EFccStatus status;
	int64_t first_pts;
	int64_t last_pts;
	int interrupt;
}ClientContext;

typedef struct FCCContext {
    const AVClass *class;
    URLContext *uc_tcp;
	int quit;
	pthread_t fcc_thread;
	pthread_t fcc_rev_thread;
    int rtp_fd, rtcp_fd, nb_ssm_include_addrs, nb_ssm_exclude_addrs;
    struct sockaddr_storage **ssm_include_addrs, **ssm_exclude_addrs;
    int write_to_source;
    struct sockaddr_storage last_rtp_source, last_rtcp_source;
    socklen_t last_rtp_source_len, last_rtcp_source_len;
    int ttl;
    int buffer_size;
    int tcp_port, local_rtpport, local_rtcpport;
    int connect;
    int pkt_size;
    int dscp;
    char *sources;
    char *block;

	EFccStatus status;
	int64_t first_pts;
	int64_t last_pts;
	int64_t receiving_pts;
	int64_t max_interval;
	int64_t min_interval;
	int64_t avg_interval;
	int64_t total_interval;
	int		interval_num;

	unsigned char *buf;
	int buf_data_len;
	pthread_mutex_t buf_mutex;
	unsigned char frag_ts[188];
	int frag_len;

	ClientContext cctx[MAX_CLIENT_NUM];
	unsigned char *client_buf;
	int client_buf_data_len;
} FCCContext;

#define OFFSET(x) offsetof(FCCContext, x)
#define D AV_OPT_FLAG_DECODING_PARAM
#define E AV_OPT_FLAG_ENCODING_PARAM

static const AVOption options[] = {
    { "buffer_size",        "Send/Receive buffer size (in bytes)",                              OFFSET(buffer_size),     AV_OPT_TYPE_INT,    { .i64 = -1 },    -1, INT_MAX, .flags = D|E },
    { "tcp_port",           "Custom tcp port",                                                  OFFSET(tcp_port),        AV_OPT_TYPE_INT,    { .i64 = -1 },    -1, INT_MAX, .flags = D|E },
    { NULL }
};

static const AVClass fcc_class = {
    .class_name = "fcc",
    .item_name  = av_default_item_name,
    .option     = options,
    .version    = LIBAVUTIL_VERSION_INT,
};


static int check_pts(unsigned char *p, int64_t *pts, int64_t *dts, int *nal_type)
{
	unsigned char *pDataStart = NULL, *es_data;
	int pes_header_data_length = 0, es_len = 0, offset;
	unsigned char payload_unit_start_indicator = 0, PTS_DTS_flags = 0, adaptation_field_control = 0, adaptation_field_length = 0, stream_id = 0;

	pDataStart = p;
	*nal_type = NAL_TYPE_UNKNOW;

	payload_unit_start_indicator = (pDataStart[1]>>6)&0x1;
	if(1 == payload_unit_start_indicator)
	{
		//av_log(NULL, AV_LOG_INFO, "[%s, %d] payload_unit_start_indicator = 1.\n", __FUNCTION__, __LINE__);
		//pid = ((pDataStart[1]&0x1F) << 8) + pDataStart[2];
		adaptation_field_control = ((pDataStart[3])&0x30)>>4;
		if(adaptation_field_control == 3 )
		{
			//one byte
			adaptation_field_length = pDataStart[4] + 1;
		}
		else if(adaptation_field_control == 1 )
		{	
			adaptation_field_length = 0;
		}
		//av_log(NULL, AV_LOG_INFO, "[%s, %d] adaptation_field_control = %d.\n", __FUNCTION__, __LINE__, adaptation_field_control);
		
		if(0x00 != pDataStart[4 + adaptation_field_length] || \
			0x00 != pDataStart[5 + adaptation_field_length] || \
			0x01 != pDataStart[6 + adaptation_field_length])
		{
			//av_log(NULL, AV_LOG_INFO, "[%s, %d].\n", __FUNCTION__, __LINE__);
			return -1;
		}

		stream_id = pDataStart[7 + adaptation_field_length];

		//pes_packet_length = (pDataStart[8 + adaptation_field_length] << 8) + pDataStart[9 + adaptation_field_length];
		
		PTS_DTS_flags = (pDataStart[11 + adaptation_field_length]>>6)&0x3;

		pes_header_data_length = pDataStart[12 + adaptation_field_length];
		
		if((0x60 != stream_id&0xC0)&&(0xE0 != stream_id&0xF0))
		{
			return -2;
		}

		if(3 == PTS_DTS_flags)
		{
			//ts header - 4 bytes
			//pes header - 6 bytes
			//pes external header - 3 bytes
			//13bytes totally
									
			*pts = ((int64_t)(pDataStart[13 + adaptation_field_length ]&0xE)    << 29) + \
				  ((int64_t) pDataStart[14 + adaptation_field_length ]          << 22) + \
				  ((int64_t)(pDataStart[15 + adaptation_field_length ]&0xFE)   << 14) + \
				  ((int64_t) pDataStart[16 + adaptation_field_length ]          << 7) + \
				  ((int64_t)(pDataStart[17 + adaptation_field_length ]&0xFE)   >> 1);
			
			*dts = ((int64_t)(pDataStart[18 + adaptation_field_length ]&0xE)    << 29) + \
				  ((int64_t) pDataStart[19 + adaptation_field_length ]          << 22) + \
				  ((int64_t)(pDataStart[20 + adaptation_field_length ]&0xFE)   << 14) + \
				  ((int64_t) pDataStart[21 + adaptation_field_length ]          << 7)  + \
				  ((int64_t)(pDataStart[22 + adaptation_field_length ]&0xFE)   >> 1);
		}
		else if(2 == PTS_DTS_flags)
		{
			//only pts
			*pts = ((int64_t)(pDataStart[13 + adaptation_field_length ]&0xE)    << 29) + \
				  ((int64_t) pDataStart[14 + adaptation_field_length ]          << 22) + \
				  ((int64_t)(pDataStart[15 + adaptation_field_length ]&0xFE)   << 14) + \
				  ((int64_t) pDataStart[16 + adaptation_field_length ]          << 7)  + \
				  ((int64_t)(pDataStart[17 + adaptation_field_length ]&0xFE)   >> 1);
			*dts = 0;

		}
		//av_log(NULL, AV_LOG_INFO, "[%s, %d] pes_header_data_length = %d.\n", __FUNCTION__, __LINE__, pes_header_data_length);
		if(pes_header_data_length){
			es_data = pDataStart + 10 + adaptation_field_length + pes_header_data_length;
			es_len = 188 - (10 + adaptation_field_length + pes_header_data_length);
			if(es_len > 0){
				for(offset = 0; offset + 4 < es_len; offset++){
					if(es_data[offset] == 0x0 && es_data[offset+1] == 0x0 && es_data[offset+2] == 0x1){
						//av_log(NULL, AV_LOG_INFO, "[%s, %d] unit type = 0x%x.\n", __FUNCTION__, __LINE__, es_data[offset + 3]&0x1F);
						if((es_data[offset + 3]&0x1F) == 1){
							*nal_type |= NAL_TYPE_NON_IDR;
						}else if((es_data[offset + 3]&0x1F) == 5){
							*nal_type |= NAL_TYPE_IDR;
						}else if((es_data[offset + 3]&0x1F) == 7){
							*nal_type |= NAL_TYPE_SPS;
						}else if((es_data[offset + 3]&0x1F) == 8){
							*nal_type |= NAL_TYPE_PPS;
						} 
					}
				}
			}
		}
		return 0;
				
	}
	else
	{
		return -3;
	}
	
}


static void  *fcc_processor(void *argv)
{
	URLContext *h = (URLContext *)*(URLContext **)argv;
	URLContext *uc_client;
	FCCContext *fcc_ctx = NULL;
	pthread_t tid;
	unsigned char rqr_msg, rsp_msg[FccSubcMsgDataLen + 1];
	unsigned char *little_buf, *buf; //[ONCE_SIZE+3];
	int ret = 0, sent = 0, len;
	int cid, rqr_ver, rqr_msg_type, rqr_sub_msg_type;	

	fcc_ctx = (FCCContext *)h->priv_data;

	tid = pthread_self();
	for(cid = 0; cid < MAX_CLIENT_NUM; cid++){
		if(tid == fcc_ctx->cctx[cid].tid)
			break;
	}
	if(MAX_CLIENT_NUM == cid){
		av_log(NULL, AV_LOG_INFO, "[%s, %d] No client number found!\n", __FUNCTION__, __LINE__);
		return NULL;
	}
	uc_client = fcc_ctx->cctx[cid].uc_tcp_client;

	av_log(NULL, AV_LOG_INFO, "[%s, %d] fcc_processor start.\n", __FUNCTION__, __LINE__);

	while(1){
		ret = ffurl_read(uc_client, &rqr_msg, 1);
		if(ret <= 0){			
			if(fcc_ctx->cctx[cid].interrupt){
				ffurl_close(uc_client);
				fcc_ctx->cctx[cid].first_pts = 0;
				fcc_ctx->cctx[cid].last_pts = 0;
				fcc_ctx->cctx[cid].status = EFccStatus_NotAvailable;
				fcc_ctx->cctx[cid].uc_tcp_client = NULL;
				//fcc_ctx->cctx[cid].tid = 0x0;
				return NULL;
			}
			usleep(1024);
			continue;
		}
		else{
			rqr_ver = rqr_msg >> 6;
			rqr_msg_type = (rqr_msg & 0x30) >> 4;
			rqr_sub_msg_type = rqr_msg & 0x0F;		
			av_log(NULL, AV_LOG_INFO, "[%s, %d] rqr_ver = %d, rqr_msg_type = %d, rqr_sub_msg_type = %d, \n", __FUNCTION__, __LINE__, rqr_ver, rqr_msg_type, rqr_sub_msg_type);

			rsp_msg[0] = FCCVERSION << 6;
			switch(rqr_msg_type)
			{
				case EFccMsgType_Requery:
					rsp_msg[0] |= EFccMsgType_Response << 4;
					switch(rqr_sub_msg_type)
					{
						case EFccSubMsgType_Status:
							rsp_msg[0] |= EFccSubMsgType_Status;
							*(EFccStatus *)(rsp_msg + 1) = fcc_ctx->status;
							break;
						case EFccSubMsgType_FstPts:
							rsp_msg[0] |= EFccSubMsgType_FstPts;
							*(int64_t *)(rsp_msg + 1) = fcc_ctx->first_pts;
							break;
						case EFccSubMsgType_LstPts:
							rsp_msg[0] |= EFccSubMsgType_LstPts;
							*(int64_t *)(rsp_msg + 1) = fcc_ctx->last_pts;
							break;
						case EFccSubMsgType_DatLen:
							rsp_msg[0] |= EFccSubMsgType_DatLen;
							*(int *)(rsp_msg + 1) = fcc_ctx->buf_data_len;
							av_log(NULL, AV_LOG_INFO, "[%s, %d] DatLen = %d.\n", __FUNCTION__, __LINE__, *(int *)(rsp_msg + 1));
							break;
						case EFccSubMsgType_MaxInt:
							rsp_msg[0] |= EFccSubMsgType_MaxInt;
							*(int64_t *)(rsp_msg + 1) = fcc_ctx->max_interval;
							break;
						case EFccSubMsgType_MinInt:
							rsp_msg[0] |= EFccSubMsgType_MinInt;
							*(int64_t *)(rsp_msg + 1) = fcc_ctx->min_interval;
							break;
						case EFccSubMsgType_AvgInt:
							rsp_msg[0] |= EFccSubMsgType_AvgInt;
							*(int64_t *)(rsp_msg + 1) = fcc_ctx->avg_interval;
							break;
						default:
							av_log(NULL, AV_LOG_INFO, "[%s, %d] rqr_sub_msg_type ERROR: Unknow\n", __FUNCTION__, __LINE__);
							break;
					}
					ret = ffurl_write(uc_client, (unsigned char *)&rsp_msg, FccSubcMsgDataLen + 1);
					av_log(NULL, AV_LOG_INFO, "[%s, %d] ffurl_write: ret = %d.\n", __FUNCTION__, __LINE__, ret);
					break;
				case EFccMsgType_Response:
					av_log(NULL, AV_LOG_INFO, "[%s, %d] rqr_msg_type ERROR: EFccMsgType_Response\n", __FUNCTION__, __LINE__);
					break;
				case EFccMsgType_Request:
					av_log(NULL, AV_LOG_INFO, "[%s, %d] EFccMsgType_Request start.\n", __FUNCTION__, __LINE__);
					pthread_mutex_lock(&fcc_ctx->buf_mutex);
					buf = av_mallocz(FCC_BUF_SIZE);
					memcpy(buf, fcc_ctx->buf, FCC_BUF_SIZE);
					len = fcc_ctx->buf_data_len;
					pthread_mutex_unlock(&fcc_ctx->buf_mutex);
					fcc_ctx->cctx[cid].client_buf = buf;
					fcc_ctx->cctx[cid].client_buf_data_len = len;

					little_buf = av_mallocz(ONCE_SIZE+3);
					while(sent < len){
						memset(little_buf, 0, ONCE_SIZE + 3);
						little_buf[0] = FCCVERSION << 6;
						little_buf[0] |= EFccMsgType_Send << 4;
						if(len - sent >= ONCE_SIZE){
							little_buf[0] |= (unsigned char)(ONCE_SIZE >> 16 & 0xF);
							little_buf[1] = (unsigned char)(ONCE_SIZE >> 8 & 0xFF);
							little_buf[2] = (unsigned char) (ONCE_SIZE & 0xFF);
							memcpy(little_buf + 3, buf + sent, ONCE_SIZE);	
							ret = ffurl_write(uc_client, little_buf, ONCE_SIZE + 3);
							if(ret < 0)
								break;
							sent += ONCE_SIZE;
						}
						else{
							little_buf[0] |= (unsigned char)((len - sent) >> 16 & 0xF);
							little_buf[1] = (unsigned char)((len - sent) >> 8 & 0xFF);
							little_buf[2] = (unsigned char) ((len - sent) & 0xFF);
							memcpy(little_buf + 3, buf + sent, (len - sent));	
							ret = ffurl_write(uc_client, little_buf, (len - sent) + 3);
							if(ret < 0)
								break;
							sent += (len - sent);
						}
						av_log(NULL, AV_LOG_INFO, "[%s, %d] ffurl_write little_buf: ret = %d.\n", __FUNCTION__, __LINE__, ret);
					}
					//send a NULL packet for ending.
					if(ret >= 0){
						memset(little_buf, 0, ONCE_SIZE + 3);
						little_buf[0] = FCCVERSION << 6;
						little_buf[0] |= EFccMsgType_Send << 4;
						ret = ffurl_write(uc_client, little_buf, 3);
						av_log(NULL, AV_LOG_INFO, "[%s, %d] ffurl_write ending little_buf: ret = %d.\n", __FUNCTION__, __LINE__, ret);
					}
					av_free(little_buf);
					little_buf = NULL;
					av_free(buf);
					fcc_ctx->cctx[cid].client_buf = buf = NULL;
					fcc_ctx->cctx[cid].client_buf_data_len = 0;
					//close
					ffurl_close(uc_client);
					fcc_ctx->cctx[cid].first_pts = 0;
					fcc_ctx->cctx[cid].last_pts = 0;
					fcc_ctx->cctx[cid].status = EFccStatus_NotAvailable;
					fcc_ctx->cctx[cid].uc_tcp_client = NULL;
					//fcc_ctx->cctx[cid].tid = 0x0;
					return NULL;
					break;
				case EFccMsgType_Send:
					av_log(NULL, AV_LOG_INFO, "[%s, %d] rqr_msg_type ERROR: EFccMsgType_Send\n", __FUNCTION__, __LINE__);
					break;
				default:
					av_log(NULL, AV_LOG_INFO, "[%s, %d] rqr_msg_type ERROR: Unknow\n", __FUNCTION__, __LINE__);
					break;
			}
			//usleep(100*1024);
		}
	}
	return NULL;
}


static void  *fcc_processor_accept(void *argv)
{
	URLContext *h = (URLContext *)*(URLContext **)argv;
	FCCContext *fcc_ctx = NULL;
	int i = 0, ret;

	av_log(NULL, AV_LOG_INFO, "[%s, %d] fcc_processor_accept start.\n", __FUNCTION__, __LINE__);
	
	fcc_ctx = (FCCContext *)h->priv_data;
	while(1){
		for(i = 0; i < MAX_CLIENT_NUM; i++){
			if(NULL == fcc_ctx->cctx[i].uc_tcp_client)
				break;
		}
		if(MAX_CLIENT_NUM == i){
			av_log(NULL, AV_LOG_INFO, "[%s, %d] MAX CLIENT NUM! Can't accept more client!\n", __FUNCTION__, __LINE__);
			break;
		}
		ret = ffurl_accept(fcc_ctx->uc_tcp, &fcc_ctx->cctx[i].uc_tcp_client);
		av_log(NULL, AV_LOG_INFO, "[%s, %d] ffurl_accept ret = %d. i = %d. filename = %s\n", __FUNCTION__, __LINE__, ret, i, fcc_ctx->cctx[i].uc_tcp_client->filename);
		
		pthread_create(&fcc_ctx->cctx[i].tid, NULL, (void *)fcc_processor, (void *)&h);
		if(fcc_ctx->quit)
			break;
	}
	
	return NULL;
}


static int fcc_open(URLContext *h, const char *uri, int flags)
{
	FCCContext *fcc_ctx = NULL;
	AVDictionary *av_options = NULL;
    char hostname[1024];
	char *p, *port_str, *url_tcp;
	int port_str_len = 0, url_tcp_len = 1024;
	int ret = 0;	

	av_log(NULL, AV_LOG_INFO, "[%s, %d] h = %x, uri = %s\n", __FUNCTION__, __LINE__, (unsigned int)h, uri);
	if(h){
		av_log(NULL, AV_LOG_INFO, "[%s, %d] h->filename = %s, h->priv_data = %x\n", __FUNCTION__, __LINE__, h->filename, (unsigned int)h->priv_data);
	}
	if(h->prot){
		av_log(NULL, AV_LOG_INFO, "[%s, %d] h->prot->name = %s\n", __FUNCTION__, __LINE__, h->prot->name);
	}
	
	//fcc_prot = h->prot;
	fcc_ctx = (FCCContext *)h->priv_data;

	fcc_ctx->buf = av_mallocz(FCC_BUF_SIZE);
	fcc_ctx->buf_data_len = 0;
	pthread_mutex_init(&fcc_ctx->buf_mutex, NULL);	

	gethostname(hostname, sizeof(hostname));

	p = strstr(uri, ":");
	port_str_len = strspn(++p, "0123456789");
	port_str = av_mallocz(port_str_len + 1);
	memcpy(port_str, p, port_str_len);
	port_str[port_str_len] = '\0';
	av_log(NULL, AV_LOG_INFO, "[%s, %d] port number = %s\n", __FUNCTION__, __LINE__, port_str);

	url_tcp = av_mallocz(url_tcp_len);
	strcat(url_tcp, "tcp://");
	strcat(url_tcp, HOST_IP);
	strcat(url_tcp, ":");
	strcat(url_tcp, port_str);
	av_log(NULL, AV_LOG_INFO, "[%s, %d] url_tcp = %s\n", __FUNCTION__, __LINE__, url_tcp);

	ret |= av_dict_set_int(&av_options, "listen", 2, 0);
	//ret |= av_dict_set_int(&av_options, "listen_timeout", 10*1024, 0);
	//ret |= av_dict_set_int(&av_options, "timeout", 1000, 0);
	ret |= av_dict_set_int(&av_options, "recv_buffer_size", TCP_RECV_BUF_SIZE, 0);
	ret |= av_dict_set_int(&av_options, "send_buffer_size", TCP_SEND_BUF_SIZE, 0);
	av_log(NULL, AV_LOG_INFO, "[%s, %d]av_dict_set_int: ret = %d\n", __FUNCTION__, __LINE__, ret);

	ret = ffurl_open_whitelist(&fcc_ctx->uc_tcp, url_tcp, AVIO_FLAG_READ_WRITE,
                                    &h->interrupt_callback, &av_options,
                                    h->protocol_whitelist, h->protocol_blacklist, h
                                   );
	av_log(NULL, AV_LOG_INFO, "[%s, %d] ffurl_open ret = %d\n", __FUNCTION__, __LINE__, ret);
	fcc_ctx->status = EFccStatus_Available;

 	pthread_create(&fcc_ctx->fcc_thread, NULL, (void *)fcc_processor_accept, (void *)&h);
	av_free(url_tcp);
	av_free(port_str);
	url_tcp = NULL;
	av_log(NULL, AV_LOG_INFO, "[%s, %d] \n", __FUNCTION__, __LINE__);
	return 0;
}

static int fcc_read(URLContext *h, uint8_t *buf, int size)
{
	av_log(NULL, AV_LOG_INFO, "[%s, %d] size = %d\n", __FUNCTION__, __LINE__, size);
	return 0;
}

static int fcc_write(URLContext *h, const uint8_t *buf, int size)
{
	FCCContext *fcc_ctx = NULL;
	int size1, i, ret, last_len = 0, nal_unit_type = 0;
	int64_t pts, dts;
	unsigned char *tempBuf = NULL;

	fcc_ctx = (FCCContext *)h->priv_data;
	last_len = fcc_ctx->buf_data_len;

	//av_log(NULL, AV_LOG_INFO, "[%s, %d] size = %d\n", __FUNCTION__, __LINE__, size);
	pthread_mutex_lock(&fcc_ctx->buf_mutex);
	if(FCC_BUF_SIZE - fcc_ctx->buf_data_len < size + fcc_ctx->frag_len)
		fcc_ctx->buf_data_len = 0;
	if(fcc_ctx->frag_len + size >= 188){		
		size1 = (size + fcc_ctx->frag_len) - (size + fcc_ctx->frag_len)%188;
		memcpy(fcc_ctx->buf + fcc_ctx->buf_data_len, &fcc_ctx->frag_ts, fcc_ctx->frag_len);
		fcc_ctx->buf_data_len += fcc_ctx->frag_len;
		memcpy(fcc_ctx->buf + fcc_ctx->buf_data_len, buf, size1 - fcc_ctx->frag_len );
		fcc_ctx->buf_data_len += (size1 - fcc_ctx->frag_len);
		memcpy(&fcc_ctx->frag_ts, buf + size1 - fcc_ctx->frag_len, size - (size1 - fcc_ctx->frag_len));
		fcc_ctx->frag_len = size - (size1 - fcc_ctx->frag_len);
	}else{
		memcpy(&fcc_ctx->frag_ts, buf, size);
		fcc_ctx->frag_len += size;
	}
	
	if(0 != fcc_ctx->buf_data_len % 188)
		av_log(NULL, AV_LOG_INFO, "[%s, %d] ERROR! buf_data_len %% 188 = %d\n", __FUNCTION__, __LINE__, fcc_ctx->buf_data_len % 188);
	
	//av_log(NULL, AV_LOG_INFO, "[%s, %d] buf_data_len = %d, last_len = %d.\n", __FUNCTION__, __LINE__, fcc_ctx->buf_data_len, last_len);
	if(fcc_ctx->buf_data_len - last_len >= 188){
		for(i = last_len / 188; i < fcc_ctx->buf_data_len / 188; i++){
			ret = check_pts(fcc_ctx->buf + i*188, &pts, &dts, &nal_unit_type);
			if(ret >= 0 && nal_unit_type > NAL_TYPE_NON_IDR){
				av_log(NULL, AV_LOG_INFO, "[%s, %d] pts = %ld, dts = %ld, nal_unit_type = %d\n", __FUNCTION__, __LINE__, pts, dts, nal_unit_type);
				// Delete old data. 
				tempBuf = av_mallocz(fcc_ctx->buf_data_len - i*188);
				memcpy(tempBuf, fcc_ctx->buf + i*188, fcc_ctx->buf_data_len - i*188);
				memcpy(fcc_ctx->buf, tempBuf, fcc_ctx->buf_data_len - i*188);
				fcc_ctx->buf_data_len = fcc_ctx->buf_data_len - i*188;
				av_free(tempBuf);
				tempBuf = NULL;
				if(0 == fcc_ctx->interval_num){
					fcc_ctx->total_interval = 0;
					fcc_ctx->max_interval = 0;
					fcc_ctx->min_interval = 0;
					fcc_ctx->avg_interval = 0;
				}
				else{
					fcc_ctx->total_interval += (pts - fcc_ctx->first_pts);
					if((pts - fcc_ctx->first_pts) > fcc_ctx->max_interval)
						fcc_ctx->max_interval = (pts - fcc_ctx->first_pts);
					if(0 == fcc_ctx->min_interval){
						fcc_ctx->min_interval = (pts - fcc_ctx->first_pts);
					}else if((pts - fcc_ctx->first_pts) < fcc_ctx->min_interval){
						fcc_ctx->min_interval = (pts - fcc_ctx->first_pts);
					}
					fcc_ctx->avg_interval = fcc_ctx->total_interval/fcc_ctx->interval_num;
				}
				fcc_ctx->interval_num++;
				fcc_ctx->first_pts = pts;
				fcc_ctx->receiving_pts = pts;
				fcc_ctx->last_pts = -1;
				break;
			}else if(ret >= 0 && NAL_TYPE_NON_IDR == nal_unit_type){
					fcc_ctx->last_pts = fcc_ctx->receiving_pts;
					fcc_ctx->receiving_pts = pts;
					break;
			}
		}
	}
	pthread_mutex_unlock(&fcc_ctx->buf_mutex);
	return 0;
}

static int fcc_close(URLContext *h)
{
	FCCContext *fcc_ctx = NULL;
	int i;

	if(!h)
		return -1;
	
	fcc_ctx = (FCCContext *)h->priv_data;

	for(i = 0; i < MAX_CLIENT_NUM; i++){
		if(fcc_ctx->cctx[i].uc_tcp_client){
			fcc_ctx->cctx[i].interrupt = 1;
			pthread_join(fcc_ctx->cctx[i].tid, NULL);
			fcc_ctx->cctx[i].tid = NULL;
		}
	}
	fcc_ctx->quit = 1;
	pthread_join(fcc_ctx->fcc_thread, NULL);
	av_log(NULL, AV_LOG_INFO, "[%s, %d] fcc_close\n", __FUNCTION__, __LINE__);
	if(fcc_ctx->buf)
		av_free(fcc_ctx->buf);
	return 0;
}

static int fcc_get_file_handle(URLContext *h)
{
	av_log(NULL, AV_LOG_INFO, "[%s, %d]\n", __FUNCTION__, __LINE__);
	return 0;
}

static int fcc_get_multi_file_handle(URLContext *h, int **handles,int *numhandles)
{
	av_log(NULL, AV_LOG_INFO, "[%s, %d]\n", __FUNCTION__, __LINE__);
	return 0;
}


const URLProtocol ff_fcc_protocol = {
    .name                      = "fcc",
    .url_open                  = fcc_open,
    .url_read                  = fcc_read,
    .url_write                 = fcc_write,
    .url_close                 = fcc_close,
    .url_get_file_handle       = fcc_get_file_handle,
    .url_get_multi_file_handle = fcc_get_multi_file_handle,
    .priv_data_size            = sizeof(FCCContext),
    .flags                     = URL_PROTOCOL_FLAG_NETWORK,
    .priv_data_class           = &fcc_class,
};

