#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <time.h>
#include <errno.h>

#ifdef _WIN32
#include <winsock2.h>
#define close closesocket
#define ioctl ioctlsocket
#ifdef errno
#undef errno
#endif
#define errno WSAGetLastError()
#ifdef EWOULDBLOCK
#undef EWOULDBLOCK
#endif
#define EWOULDBLOCK WSAEWOULDBLOCK
#else
#include <netdb.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <unistd.h>
#endif

#ifdef _WIN32
#define msleep Sleep
#else
static void msleep(int ms)
{
	struct timespec tv;
	tv.tv_sec = (ms) / 1000;
	tv.tv_nsec = ((ms) % 1000) * 1000 * 1000;
	nanosleep(&tv, &tv);
}
#endif

#if USE_SSL
#include "openssl/err.h"
#include "openssl/ssl.h"
#endif

#define DEFAULT_CIPHERS "HIGH:!aNULL" /* EECDH+AESGCM:EDH+AESGCM:EECDH+AES256:EDH+AES256 */

#include "internal.h"
#include "network.h"

#if USE_SSL
static int g_ctx_use_cnt = 0;
static SSL_CTX *g_ctx = NULL;
#endif

int net_connect(const char *hostname, unsigned port, int udp, int nodelay, int nonblock)
{
	struct addrinfo hints, *result, *rp;
	int fd, status;

	memset(&hints, 0, sizeof(struct addrinfo));
	hints.ai_family = AF_UNSPEC;
	hints.ai_socktype = udp ? SOCK_DGRAM : SOCK_STREAM;
    hints.ai_flags = hostname ? 0 : AI_PASSIVE;
    char svc[20];
    sprintf(svc, "%u", port);

	if ((status = getaddrinfo(hostname, svc, &hints, &result)) != 0)
		return -1;

	for (rp = result; rp != NULL; rp = rp->ai_next) {
		fd = socket(rp->ai_family, rp->ai_socktype, rp->ai_protocol);

		if (fd == -1)
		   continue;

		if (connect(fd, rp->ai_addr, rp->ai_addrlen) != -1)
			break;

		close(fd);
	}

	freeaddrinfo(result);

	if (rp == NULL)
		return -1;

	struct linger l;
	l.l_onoff = 0;
	l.l_linger = 1;
	setsockopt(fd, SOL_SOCKET, SO_LINGER, (char*)&l, sizeof(l));
	int flag = 1;
	setsockopt(fd, SOL_SOCKET, SO_KEEPALIVE, (char*)&flag, sizeof(flag));
	flag = nodelay;
	setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, (char*)&flag, sizeof(flag));

#ifdef TCP_QUICKACK
	flag = 1;
	setsockopt(fd, IPPROTO_TCP, TCP_QUICKACK, (char*)&flag, sizeof(flag));
#endif

	if (nonblock) {
		unsigned long flag = 1;
		ioctl(fd, FIONBIO, &flag);
	}

	return fd;
}

int net_server(const char *hostname, unsigned port, int udp, int nonblock)
{
	struct addrinfo hints, *result, *rp;
	int fd, status;

	memset(&hints, 0, sizeof(struct addrinfo));
	hints.ai_family = AF_UNSPEC;
	hints.ai_socktype = udp ? SOCK_DGRAM : SOCK_STREAM;
    hints.ai_flags = AI_PASSIVE;
    char svc[20];
    sprintf(svc, "%u", port);

	if ((status = getaddrinfo(NULL, svc, &hints, &result)) != 0) {
		perror("getaddrinfo");
		return -1;
	}

	for (rp = result; rp != NULL; rp = rp->ai_next) {
		fd = socket(rp->ai_family, rp->ai_socktype, rp->ai_protocol);

		if (fd == -1)
		   continue;

		if (bind(fd, rp->ai_addr, rp->ai_addrlen) == 0)
			break;

		close(fd);
	}

	freeaddrinfo(result);

	if (rp == NULL)
		return -1;

	if (nonblock) {
		unsigned long flag = 1;
		ioctl(fd, FIONBIO, &flag);
	}

	if (udp)
		return fd;

	listen(fd, 4096);
	return fd;
}

int net_accept(stream *str)
{
	struct sockaddr_in addr;
	socklen_t len;
	int fd = accept(fileno(str->fp), (struct sockaddr*)&addr, &len);

	if ((fd == -1) && ((errno == EWOULDBLOCK) || (errno == EAGAIN)))
		return -1;

	struct linger l;
	l.l_onoff = 0;
	l.l_linger = 1;
	setsockopt(fd, SOL_SOCKET, SO_LINGER, (char*)&l, sizeof(l));
	int flag = 1;
	setsockopt(fd, SOL_SOCKET, SO_KEEPALIVE, (char*)&flag, sizeof(flag));
	flag = str->nodelay;
	setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, (char*)&flag, sizeof(flag));

	if (str->nonblock) {
		unsigned long flag = 1;
		ioctl(fd, FIONBIO, &flag);
	}

	return fd;
}

#if USE_SSL
void *net_enable_ssl(int fd, const char *hostname)
{
	if (!g_ctx_use_cnt++) {
		g_ctx = SSL_CTX_new(TLS_client_method());
		//SSL_CTX_set_options(g_ctx, SSL_OP_NO_SSLv2 | SSL_OP_NO_SSLv3);
		//SSL_CTX_set_cipher_list(g_ctx, DEFAULT_CIPHERS);
	}

	SSL *ssl = SSL_new(g_ctx);
	//SSL_set_ssl_method(ssl, TLS_client_method());
	//SSL_set_mode(ssl, SSL_MODE_AUTO_RETRY);
	//SSL_set_verify(ssl, SSL_VERIFY_NONE, 0);
	SSL_set_tlsext_host_name(ssl, hostname);
	SSL_set_fd(ssl, fd);
	int status = 0, cnt = 0;

	while ((status = SSL_connect(ssl)) == -1) {
		if ((cnt++) > (5*1000))
			break;

		msleep(1);
	}

	if (status <= 0) {
		fprintf(stderr, "SSL_connect failed\n");
		ERR_print_errors_fp(stderr);
		return 0;
	}

	return ssl;
}

size_t ssl_write(const void *ptr, size_t nbytes, stream *str)
{
	return SSL_write((SSL*)str->sslptr, ptr, nbytes);
}

size_t ssl_read(void *ptr, size_t len, stream *str)
{
	char *dst = ptr;

	while (len && str->srclen) {
		*dst++ = *str->src++;
		str->srclen--;
		len--;
	}

	if (dst != ptr) {
		return dst - (char*)ptr;
	}

	return SSL_read((SSL*)str->sslptr, ptr, len);
}

int ssl_getline(char **lineptr, size_t *n, stream *str)
{
	if (!*lineptr)
		*lineptr = malloc(*n=1024);

	char *dstptr = *lineptr;
	size_t dstlen = *n;
	int done = 0;

	while (!done) {
		if (str->srclen <= 0) {
			int rlen = SSL_read((SSL*)str->sslptr, str->srcbuf, STREAM_BUFLEN);

			if (rlen <= 0)
				return -1;

			str->srcbuf[rlen] = '\0';
			str->src = str->srcbuf;
			str->srclen = rlen;
		}

		while (str->srclen-- > 0) {
			int ch = *str->src++;
			*dstptr++ = ch;

			if (dstlen-- <= 1) {
				size_t savelen = dstptr - *lineptr;
				*lineptr = realloc(*lineptr, *n *= 2);
				dstptr = *lineptr + savelen;
				dstlen = *n - savelen;
			}

			if (ch == '\n') {
				*dstptr = '\0';
				done = 1;
				break;
			}
		}
	}

	return dstptr - *lineptr;
}

void ssl_close(stream *str)
{
	SSL_shutdown((SSL*)str->sslptr);
	SSL_free((SSL*)str->sslptr);

	if (!--g_ctx_use_cnt)
		SSL_CTX_free(g_ctx);
}
#endif
