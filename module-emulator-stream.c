#include "globals.h"

#ifdef WITH_EMU
#include "cscrypt/des.h"
#include "oscam-string.h"
#include "oscam-config.h"
#include "oscam-time.h"
#else
#include "des.h"
#endif

#include "ffdecsa/ffdecsa.h"
#include "module-emulator-osemu.h"
#include "module-emulator-stream.h"

#ifndef WITH_EMU
#include <signal.h>
#endif

extern int32_t exit_oscam;
int8_t stream_server_thread_init = 0;
int32_t emu_stream_source_port = 8001;
int32_t emu_stream_relay_port = 17999;
unsigned char emu_stream_source_ip[16] = {"127.0.0.1"};

#ifdef WITH_EMU
pthread_mutex_t emu_fixed_key_data_mutex;
emu_stream_client_data emu_fixed_key_data;
uint16_t emu_stream_cur_srvid = 0;
LLIST *ll_emu_stream_delayed_keys;
int8_t stream_server_has_ecm = 0;
#endif
int our_pid;

static int32_t glistenfd, gconnfd;

static void SearchTsPackets(uint8_t *buf, uint32_t bufLength, uint16_t *packetCount, uint16_t *packetSize, uint16_t *startOffset)
{
	uint32_t i;
	
	(*packetCount) = 0;
	(*packetSize) = 0;
	(*startOffset) = 0;

	for(i=0; i<bufLength; i++) {	
		if(buf[i] == 0x47) {
			if((buf[i+188] == 0x47) & (buf[i+376] == 0x47)) {  //if three packets align, probably safe to assume correct size.
				(*packetSize) = 188;
				(*startOffset) = i;
				return;
			}
			else if((buf[i+204] == 0x47) & (buf[i+408] == 0x47)) {
				(*packetSize) = 204;
				(*startOffset) = i;
				return;
			}
			else if((buf[i+208] == 0x47) & (buf[i+416] == 0x47)) {
				(*packetSize) = 208;
				(*startOffset) = i;
				return;
			}					
		}	
		
	}
	
}

typedef void (*ts_data_callback)(emu_stream_client_data *cdata);

static void ParseTSData(uint8_t table_id, uint8_t table_mask, uint8_t min_table_length, int8_t* flag, uint8_t* data,
							uint16_t data_length, uint16_t* data_pos, int8_t payloadStart, uint8_t* buf, int32_t len,
							ts_data_callback func, emu_stream_client_data *cdata)
{
	uint16_t section_length;
	int32_t i;
	int8_t found_start = 0;
	uint16_t offset = 0;
	int32_t free_data_length;
	int32_t copySize;
	
	if(len < 1)
		{ return; }
	
	if(*flag == 0 && !payloadStart)
		{ return; }

	if(*flag == 0)
	{ 
		*data_pos = 0;
		 offset = 1 + buf[0];
	}
	else if(payloadStart)
	{ 
		offset = 1; 
	}
	
	if(len-offset < 1)
		{ return; }
	
	free_data_length = data_length - *data_pos;
	copySize = (len-offset) > free_data_length ? free_data_length : (len-offset);
	
	memcpy(data+(*data_pos), buf+offset, copySize);	
	(*data_pos) += copySize;

	found_start = 0;
	for(i=0; i < *data_pos; i++)
	{
		if((data[i] & table_mask) == table_id)
		{
			if(i != 0)
			{
				if((*data_pos)-i > i)
					{ memmove(data, &data[i], (*data_pos)-i); }
				else
					{ memcpy(data, &data[i], (*data_pos)-i); }
			
				*data_pos -= i;
			}
			found_start = 1;
			break;
		}	
	}
	if(!found_start)
		{ *flag = 0; return; }

	*flag = 2;

	if(*data_pos < 3)
		{ return; }

	section_length = SCT_LEN(data);

	if(section_length > data_length || section_length < min_table_length)
		{ *flag = 0; return; }
	
	if((*data_pos) < section_length)
		{ return; }

	func(cdata);
	
	found_start = 0;
	for(i=section_length; i < *data_pos; i++)
	{
		if((data[i] & table_mask) == table_id)
		{
			if((*data_pos)-i > i)
				{ memmove(data, &data[i], (*data_pos)-i); }
			else
				{ memcpy(data, &data[i], (*data_pos)-i); }
			
			*data_pos -= i;
			found_start = 1;
			break;
		}	
	}	
	if(!found_start)
		{ *data_pos = 0; }
	
	*flag = 1;
}

static void ParsePATData(emu_stream_client_data *cdata)
{
	uint8_t* data = cdata->data;
	uint16_t section_length = SCT_LEN(data);
	uint16_t srvid;
	int32_t i;

	for(i=8; i+7<section_length; i+=4)
	{
		srvid = b2i(2, data+i);
		
		if(srvid == 0)
			{ continue; }
		
		if(cdata->srvid == srvid)
		{
			cdata->pmt_pid = b2i(2, data+i+2) & 0x1FFF;
			cs_log_dbg(D_READER, "[Emu] stream found pmt pid: %X", cdata->pmt_pid);
			break;
		}
	}
}

static void ParsePMTData(emu_stream_client_data *cdata)
{
	uint8_t* data = cdata->data;
	
	uint16_t section_length = SCT_LEN(data);
	int32_t i;
	uint16_t program_info_length = 0, es_info_length = 0;
	uint8_t descriptor_tag = 0, descriptor_length = 0;
	uint8_t stream_type;
	uint16_t stream_pid, caid;
	
	program_info_length = b2i(2, data+10) &0xFFF;
	
	if(12+program_info_length >= section_length)
		{ return; }
	
	for(i=12; i+1 < 12+program_info_length; i+=descriptor_length+2)
	{
		descriptor_tag = data[i];
		descriptor_length = data[i+1];
		
		if(descriptor_length < 1)
			{ break; }
			
		if(i+1+descriptor_length >= 12+program_info_length)
			{ break; }
		
		if(descriptor_tag == 0x09 && descriptor_length >= 4)
		{
			caid = b2i(2, data+i+2);
			
			if(caid>>8 == 0x0E)
			{
		    	cdata->ecm_pid = b2i(2, data+i+4) &0x1FFF;
		    	cs_log_dbg(D_READER, "[Emu] stream found ecm_pid: %X", cdata->ecm_pid);
		    	break;
		    }
		}
	}
		
	for(i=12+program_info_length; i+4<section_length; i+=5+es_info_length)
	{
		stream_type = data[i];
		stream_pid = b2i(2, data+i+1) &0x1FFF;
		es_info_length = b2i(2, data+i+3) &0xFFF;
		
		if(stream_type == 0x01 || stream_type == 0x02 || stream_type == 0x10 || stream_type == 0x1B 
			|| stream_type == 0x24 || stream_type == 0x42 || stream_type == 0xD1 || stream_type == 0xEA) 
		{ 
			cdata->video_pid = stream_pid;
			cs_log_dbg(D_READER, "[Emu] stream found video pid: %X", stream_pid);
		}
		
		if(stream_type == 0x03 || stream_type == 0x04 || stream_type == 0x06 || stream_type == 0x0F 
			|| stream_type == 0x11 || (stream_type >= 0x80 && stream_type <= 0x87))
		{
			if(cdata->audio_pid_count >= 4)
				{ continue; }
			
			cdata->audio_pids[cdata->audio_pid_count] = stream_pid;
			cdata->audio_pid_count++;
			cs_log_dbg(D_READER, "[Emu] stream found audio pid: %X", stream_pid);
		}
	}
}

static void ParseECMData(emu_stream_client_data *cdata)
{
	uint8_t* data = cdata->data;
	uint16_t section_length = SCT_LEN(data);
	uint8_t dcw[16];
	
	if(section_length < 0xb)
		{ return; }

	if(data[0xb] > cdata->ecm_nb || (cdata->ecm_nb == 255 && data[0xb] == 0)
		|| ((cdata->ecm_nb - data[0xb]) > 5))
	{
		cdata->ecm_nb = data[0xb];
		PowervuECM(data, dcw, cdata, 0);
	}
}

static void ParseTSPackets(emu_stream_client_data *data, uint8_t *stream_buf,  uint32_t bufLength, uint16_t packetSize)
{
	uint32_t i, j, k;
	uint32_t tsHeader;
	uint16_t pid, offset;
	uint8_t scramblingControl, payloadStart, oddeven;
	int8_t oddKeyUsed;
	uint32_t *deskey;
	uint8_t *pdata;
	uint8_t *packetClusterA[4][128];  //separate cluster arrays for video and each audio track
	uint8_t *packetClusterV[512];
	void *csakeyA[4];
	void *csakeyV;
	emu_stream_client_data *keydata;
	uint32_t scrambled_packets;

	packetClusterV[0] = NULL;
	scrambled_packets = 0;  // a counter for how many scrambled video packets (mostly for debugging)
	uint32_t cs =0;  //video cluster start
	uint32_t ce =1;  //video cluster end
	uint32_t csa[4];  //cluster index for audio tracks
	
	for(i=0; i<bufLength; i+=packetSize)  // process all packets in buffer
	{		
		tsHeader = b2i(4, stream_buf+i);
		pid = (tsHeader & 0x1fff00) >> 8;
		scramblingControl = tsHeader & 0xc0;
		payloadStart = (tsHeader & 0x400000) >> 22;

		if(tsHeader & 0x20)
			{ offset = 4 + stream_buf[i+4] + 1; }
		else
			{ offset = 4; }
		
		if(packetSize-offset < 1)
			{ continue; }
		
		if(data->have_pat_data != 1)
		{					
			if(pid == 0)
			{ 
				ParseTSData(0x00, 0xFF, 16, &data->have_pat_data, data->data, sizeof(data->data), &data->data_pos, payloadStart, 
								stream_buf+i+offset, packetSize-offset, ParsePATData, data);
			}
		
			continue;
		}

		if(!data->pmt_pid)
		{
			data->have_pat_data = 0;
			continue;
		}

		if(data->have_pmt_data != 1)
		{
			if(pid == data->pmt_pid)
			{
				ParseTSData(0x02, 0xFF, 21, &data->have_pmt_data, data->data, sizeof(data->data), &data->data_pos, payloadStart, 
								stream_buf+i+offset, packetSize-offset, ParsePMTData, data);
			}
		
			continue;
		}

		if(data->ecm_pid && pid == data->ecm_pid)
		{
#ifdef WITH_EMU
			stream_server_has_ecm = 1;
#endif
			
			ParseTSData(0x80, 0xFE, 10, &data->have_ecm_data, data->data, sizeof(data->data), &data->data_pos, payloadStart, 
							stream_buf+i+offset, packetSize-offset, ParseECMData, data);
//	printf("New ecm packet...\n");
			continue;
		}
		
		if(scramblingControl == 0)
			{ continue; }
		
		if(!(stream_buf[i+3] & 0x10))
		{
			stream_buf[i+3] &= 0x3F;
			continue;
		}

		oddKeyUsed = scramblingControl == 0xC0 ? 1 : 0;
//printf("oddKeyUsed = %i\n",oddKeyUsed);
#ifdef WITH_EMU	
		if(!stream_server_has_ecm)
		{
			keydata = &emu_fixed_key_data;
			SAFE_MUTEX_LOCK(&emu_fixed_key_data_mutex); 
		}
		else
		{
#endif
			keydata = data;
#ifdef WITH_EMU
		}
#endif
		
		if(keydata->pvu_csa_used)
		{
//	printf("New CSAA   packet...\n");
//	printf("scramblingControl=%i\n",scramblingControl);
			oddeven = scramblingControl;  // for detecting odd/even switch
			csakeyV = NULL;
			csakeyA[0] = NULL;
			csakeyA[1] = NULL;
			csakeyA[2] = NULL;
			csakeyA[3] = NULL;
			
			if(pid == data->video_pid)   // start with video pid, since it is most dominant
			{
				csakeyV = keydata->pvu_csa_ks[PVU_CW_VID];
						
				if(csakeyV !=NULL) 
				{
					for(k=0; k<data->audio_pid_count; k++)
						{
							csakeyA[k] = keydata->pvu_csa_ks[PVU_CW_A1+k];
							csa[k]=0;
						}
					scrambled_packets=0;
					cs=0;
					ce=1;
					packetClusterV[cs] = stream_buf+i;  // set first cluster start
					scrambled_packets++;
					for(j=i+packetSize;j<bufLength;j+=packetSize)   // Now iterate through the rest of the packets and create clusters for batch decryption
					{
						tsHeader = b2i(4, stream_buf+j);
						pid = (tsHeader & 0x1fff00) >> 8;
						if(pid == data->video_pid) 
						{
							if (oddeven != (tsHeader & 0xc0)) // changed key so stop adding clusters
							{
//	printf("New key video...\n");
//	printf("scramblingControl=%i\n",scramblingControl);
//	printf("oddeven=%i   header=%i\n",oddeven,(tsHeader & 0xc0));
								break;
							}
							if (cs > ce) {		// First video packet for each cluster
								packetClusterV[cs] = stream_buf+j;
								ce = cs +1;
							}

							scrambled_packets++;
						}
						else
						{
							if ( cs < ce) {		// First non-video packet - need to set end of video cluster 
								packetClusterV[ce] = stream_buf+j -1;
								cs = ce +1;
							}
							for(k=0; k<data->audio_pid_count; k++)  // Check for audio tracks and create single packet clusters
							{
								if(pid == data->audio_pids[k])
								{					
									packetClusterA[k][csa[k]] = stream_buf+j;
									csa[k]++;
									packetClusterA[k][csa[k]] = stream_buf+j+packetSize -1;
									csa[k]++;
								}			
							}
						}
					}
//	printf("cs =%i ce=%i\n",cs,ce);
					if ( cs > ce )  // last packet was not a video packet, so set null for end of all clusteers
					{packetClusterV[cs] = NULL;}
					else 
					{
						if(scrambled_packets==1) // Just in case only one video packet was found
						{
							packetClusterV[ce] = stream_buf+i+packetSize -1;
						}
						else  // last packet was a video packet, so set end of cluster to end of last packet
						{
							packetClusterV[ce] = stream_buf+j -1;
						}
						packetClusterV[ce+1] = NULL;  // add null to end of cluster list
					}
//	printf("scrambled_packets=%i\n",scrambled_packets);
					if(scrambled_packets>1) j = decrypt_packets(csakeyV, packetClusterV);
//	printf("descrambled_packets=%i\n",j);
					scrambled_packets = scrambled_packets - j;  // for debugging

					for(k=0; k<data->audio_pid_count; k++)
					{
						if(csakeyA[k] != NULL)  // if audio track has key, set null to mark end and decrypt
						{
//	printf("csa k=%i csa[k]=%i\n",k,csa[k]);
							packetClusterA[k][csa[k]] = NULL;
							decrypt_packets(csakeyA[k], packetClusterA[k]);
						}
					}
				}			
			}		
	// Old audio decrypt	 Check here for any audio packets which weren't already decryptted...
			else
			{
				for(j=0; j<data->audio_pid_count; j++)
					if(pid == data->audio_pids[j])
						{ csakeyA[0] = keydata->pvu_csa_ks[PVU_CW_A1+j]; }
			
				if(csakeyA[0] != NULL)
				{					
//	printf("csa single audio\n");
					packetClusterA[0][0] = stream_buf+i;
					packetClusterA[0][1] = stream_buf+i+packetSize -1;
					packetClusterA[0][2] = NULL;
					decrypt_packets(csakeyA[0], packetClusterA[0]);
				}			
			}			
		}
		else
		{
//	printf("New DES   packet...\n");
			deskey = NULL;
			
			if(pid == data->video_pid)
				{ deskey = keydata->pvu_des_ks[PVU_CW_VID][oddKeyUsed]; }
			else
			{
				for(j=0; j<data->audio_pid_count; j++)
					if(pid == data->audio_pids[j])
						{ deskey = keydata->pvu_des_ks[PVU_CW_A1+j][oddKeyUsed]; }
			}
			
			if(deskey != NULL)
			{					
				for(j=offset; j+7<188; j+=8)
				{
					pdata = stream_buf+i+j;
					des(pdata, deskey, 0);
				}
				
				stream_buf[i+3] &= 0x3F;
			}
		}

#ifdef WITH_EMU	
		if(!stream_server_has_ecm)
		{
			SAFE_MUTEX_UNLOCK(&emu_fixed_key_data_mutex); 
		}
#endif
	}
//	printf("scrambled_packets remaining      =%i\n",scrambled_packets);
}

static int32_t connect_to_stream(char *http_buf, int32_t http_buf_len, char *stream_path)
{
	struct sockaddr_in cservaddr;
		
	int32_t streamfd = socket(AF_INET, SOCK_STREAM, 0);
	if(streamfd == -1)
		{ return -1; }
	
	bzero(&cservaddr, sizeof(cservaddr));
	cservaddr.sin_family = AF_INET;
	cservaddr.sin_addr.s_addr = inet_addr((const char *)emu_stream_source_ip);
	cservaddr.sin_port = htons(emu_stream_source_port);
	
	if(connect(streamfd, (struct sockaddr *)&cservaddr, sizeof(cservaddr)) == -1)
		{ return -1; }
			
	snprintf(http_buf, http_buf_len, "GET %s HTTP/1.1\nHost: %s:%u\n"
				"User-Agent: Mozilla/5.0 (Windows NT 6.1; WOW64; rv:38.0) Gecko/20100101 Firefox/38.0\n"
				"Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\n"
				"Accept-Language: en-US\n"
				"Connection: keep-alive\n\n", stream_path,  emu_stream_source_ip, emu_stream_source_port);

	if(send(streamfd, http_buf, strlen(http_buf), 0) == -1)
		{ return -1; }
		
	return streamfd;	
}

static void handle_stream_client(int32_t connfd)
{
#define EMU_DVB_MAX_TS_PACKETS 256
#define EMU_DVB_BUFFER_SIZE 188*EMU_DVB_MAX_TS_PACKETS  // Set buffer to align to packets (probably should do it dynamically to account for other sizes...
#define EMU_DVB_BUFFER_WAIT 188*(EMU_DVB_MAX_TS_PACKETS-128) // we want lots of packets for parallel batch decryption advantage

	char *http_buf, stream_path[255], stream_path_copy[255];
	int32_t streamfd;
	int32_t clientStatus, streamStatus;
	uint8_t *stream_buf;
	uint16_t packetCount = 0, packetSize = 0, startOffset = 0;
	uint32_t remainingDataPos, remainingDataLength;
	int32_t bytesRead = 0;
	emu_stream_client_data *data;
	int8_t streamErrorCount = 0;
	int32_t i, srvidtmp;
	char *saveptr, *token;
	
	if(!cs_malloc(&http_buf, 1024))
	{
		close(connfd);
		return;
	}
	
	if(!cs_malloc(&stream_buf, EMU_DVB_BUFFER_SIZE))
	{
		close(connfd);
		NULLFREE(http_buf);
		return;
	}
	
	if(!cs_malloc(&data, sizeof(emu_stream_client_data)))
	{
		close(connfd);
		NULLFREE(http_buf);
		NULLFREE(stream_buf);
		return;
	}
	
	clientStatus = recv(connfd, http_buf, 1024, 0);
	if(clientStatus < 1)
	{
		close(connfd);
		NULLFREE(http_buf);
		NULLFREE(stream_buf);
		NULLFREE(data);
		return;		
	}
	
	http_buf[1023] = '\0';
	if(sscanf(http_buf, "GET %254s ", stream_path) < 1)
	{
		close(connfd);
		NULLFREE(http_buf);
		NULLFREE(stream_buf);
		NULLFREE(data);
		return;
	}
	
	cs_strncpy(stream_path_copy, stream_path, sizeof(stream_path));
	
	token = strtok_r(stream_path_copy, ":", &saveptr);

	for(i=0; token != NULL && i<3; i++)
	{
		token = strtok_r(NULL, ":", &saveptr);
		if(token == NULL)
			{ break; }
	}
	if(token != NULL)
	{
		if(sscanf(token, "%x", &srvidtmp) < 1)
		{
			token = NULL;	
		}
		else
		{
			data->srvid = srvidtmp & 0xFFFF;
		}
	}

	if(token == NULL)
	{
		close(connfd);
		NULLFREE(http_buf);
		NULLFREE(stream_buf);
		NULLFREE(data);
		return;
	}

#ifdef WITH_EMU
	emu_stream_cur_srvid = data->srvid;
	stream_server_has_ecm = 0;
#endif

	cs_log("[Emu] stream client connected with request %s", stream_path);

	snprintf(http_buf, 1024, "HTTP/1.0 200 OK\nConnection: Close\nContent-Type: video/mpeg\nServer: stream_enigma2\n\n");
	clientStatus = send(connfd, http_buf, strlen(http_buf), 0);

	while(!exit_oscam && clientStatus != -1 && streamErrorCount < 3)
	{		
		streamfd = connect_to_stream(http_buf, 1024, stream_path);
		if(streamfd == -1)
		{
			cs_log("[Emu] warning: cannot connect to stream source");
			streamErrorCount++;
			cs_sleepms(100);
			continue;	
		}

		streamErrorCount = 0;
		streamStatus = 0;
		bytesRead = 0;

		while(!exit_oscam && clientStatus != -1 && streamStatus != -1 && streamErrorCount < 3)
		{
			streamStatus = recv(streamfd, stream_buf+bytesRead, EMU_DVB_BUFFER_SIZE-bytesRead, MSG_WAITALL);  
			//WAIT for full buffer - no memcpy needed and no need for looping for multiple recvs.
			if(streamStatus == -1)
				{ break; }
		
			if(streamStatus == 0)
			{
				cs_log("[Emu] warning: no data from stream source");
				streamErrorCount++;
				cs_sleepms(100);
				continue;	
			}

			bytesRead += streamStatus;
			
			if(bytesRead >= EMU_DVB_BUFFER_WAIT) //still check in case recv was interuppted and returned non-full buffer
			{	
				startOffset = 0;
				if( stream_buf[0] != 0x47 || packetSize == 0)  // only search if not starting on ts packet or unknown packet size 
				{	
//printf("packetSize=%i  buf=%x\n",packetSize,stream_buf[0]);
					SearchTsPackets(stream_buf, bytesRead, &packetCount, &packetSize, &startOffset);
				}
				if(packetSize == 0)
				{
					bytesRead = 0;
				}
				else
				{
					packetCount = ((bytesRead-startOffset) / packetSize); // Simpler method to count packets
//printf("packetCount=%i\n",packetCount);

//if ( startOffset !=0 ) printf("startOffset=%i\n\n",startOffset);
//printf("packetCount=%i   bytesRead=%i\n",packetCount, bytesRead);

					ParseTSPackets(data, stream_buf+startOffset, packetCount*packetSize, packetSize);
					
					clientStatus = send(connfd, stream_buf+startOffset, packetCount*packetSize, 0);
						 
					remainingDataPos = startOffset+(packetCount*packetSize);
					remainingDataLength = bytesRead-remainingDataPos;
					
					if(remainingDataPos < remainingDataLength)
						{ memmove(stream_buf, stream_buf+remainingDataPos, remainingDataLength); }
					else
						{ memcpy(stream_buf, stream_buf+remainingDataPos, remainingDataLength); }
					
					bytesRead = remainingDataLength;
//printf("RemaingBytes=%i\n",bytesRead);
					if (clientStatus < packetCount*packetSize) {     //could buffer client data, but probably just dropping is ok
						printf("clientStatus=%i\n",clientStatus);
						printf("bytesRead=%i\n",packetCount*packetSize);
					}
				}
			}
		}
//printf("streamErrorCount=%i\n",streamErrorCount);
//printf("streamStatus=%i\n",streamStatus);
//printf("streamErrorCount=%i\n",streamErrorCount);
		
		close(streamfd);
		streamErrorCount = 0;
	}
	
	close(connfd);
	NULLFREE(http_buf);
	NULLFREE(stream_buf);
	for(i=0; i<8; i++)
	{
		if(data->pvu_csa_ks[i])
			{ free_key_struct(data->pvu_csa_ks[i]); }	
	}
	NULLFREE(data);
}

void *stream_server(void *UNUSED(a))
{
	struct sockaddr_in servaddr, cliaddr;
	socklen_t clilen;
	int32_t reuse = 1;
	signal(SIGCHLD, SIG_IGN);	
	glistenfd = socket(AF_INET, SOCK_STREAM, 0);
	if(glistenfd == -1)
	{
		cs_log("[Emu] error: cannot create stream server socket");
		return NULL;
	}

	bzero(&servaddr,sizeof(servaddr));
	servaddr.sin_family = AF_INET;
	servaddr.sin_addr.s_addr = htonl(INADDR_ANY);
	servaddr.sin_port = htons(emu_stream_relay_port);
	setsockopt(glistenfd, SOL_SOCKET, SO_REUSEADDR, &reuse, sizeof(reuse));
	
	if(bind(glistenfd,(struct sockaddr *)&servaddr, sizeof(servaddr)) == -1)
	{
		cs_log("[Emu] error: cannot bind to stream server socket");
		close(glistenfd);
		return NULL;
	}
	
	if(listen(glistenfd, 3) == -1)
	{
		cs_log("[Emu] error: cannot listen to stream server socket");
		close(glistenfd);
		return NULL;
	}

	while(!exit_oscam)
  	{
		clilen = sizeof(cliaddr);
		gconnfd = accept(glistenfd,(struct sockaddr *)&cliaddr, &clilen);

		if(gconnfd == -1)
		{
			cs_log("[Emu] error: accept() failed");
			break;
		}
	
#ifndef WITH_EMU
		/* Create child process */
	      our_pid = fork();
	      cs_log("[Emu] FORK pid: %i",our_pid);
		if (our_pid < 0)
	       	{
	        perror("ERROR on fork");
	        exit(1);
	        }
     
	      if (our_pid == 0)
	        {
	        /* This is the client process */
	        close(glistenfd);
#endif
		handle_stream_client(gconnfd);
		cs_log("[Emu] stream client disconnected");
#ifndef WITH_EMU
     		exit(0);
	        }
	      else
	         {
	         close(gconnfd);
	         }	
#endif
	} 
	
	close(glistenfd);
	
	return NULL;
}

#ifdef WITH_EMU
void *stream_key_delayer(void *UNUSED(a))
{
	int32_t j;
	emu_stream_client_data* cdata = &emu_fixed_key_data;
	emu_stream_cw_item *item;
	
	while(!exit_oscam)
	{
		item = ll_remove_first(ll_emu_stream_delayed_keys);
		
		if(item)
		{
			cs_sleepms(cfg.emu_stream_ecm_delay);
	    	
			SAFE_MUTEX_LOCK(&emu_fixed_key_data_mutex);
	    	
			for(j=0; j<8; j++)
			{
				if(item->csa_used)
				{	
					if(cdata->pvu_csa_ks[j] == NULL)
						{  cdata->pvu_csa_ks[j] = get_key_struct(); }
						
					if(item->is_even)
						{ set_even_control_word(cdata->pvu_csa_ks[j], item->cw[j]); }
					else
						{ set_odd_control_word(cdata->pvu_csa_ks[j], item->cw[j]); }
					
					cdata->pvu_csa_used = 1;
				}
				else
				{					
					if(item->is_even)
						{ des_set_key(item->cw[j], cdata->pvu_des_ks[j][0]); }
					else
						{ des_set_key(item->cw[j], cdata->pvu_des_ks[j][1]); }
						
					cdata->pvu_csa_used = 0;
				}
			}
							
			SAFE_MUTEX_UNLOCK(&emu_fixed_key_data_mutex);
			
			free(item);
		}
		else
		{
			cs_sleepms(50);	
		}
	}
	
	return NULL;
}
#endif

void stop_stream_server(void)
{
	shutdown(gconnfd, 2);
	shutdown(glistenfd, 2);
	close(gconnfd);
	close(glistenfd);	
}
