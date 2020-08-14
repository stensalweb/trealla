#pragma once

int net_server(const char *hostname, unsigned port, int udp, int nonblock);
int net_accept(stream *str);
int net_connect(const char *hostname, unsigned port, int udp, int nodelay, int nonblock);

#if USE_SSL
void *net_enable_ssl(int fd, const char *hostname);
size_t ssl_read(void *ptr, size_t len, stream *str);
int ssl_getline(char **lineptr, size_t *n, stream *str);
size_t ssl_write(const void *ptr, size_t nbytes, stream *str);
void ssl_close(stream *str);
#endif
