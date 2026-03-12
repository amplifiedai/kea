#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifndef _WIN32
#include <netdb.h>
#include <sys/socket.h>
#include <unistd.h>
#endif

static const char KEA_EMPTY_STRING[] = "";

int8_t __kea_io_write_file(const char *path, const char *data) {
  if (path == NULL || data == NULL) {
    return -1;
  }

  FILE *file = fopen(path, "wb");
  if (file == NULL) {
    return -1;
  }

  size_t len = strlen(data);
  size_t written = fwrite(data, 1, len, file);
  int closed = fclose(file);
  return (written == len && closed == 0) ? 0 : -1;
}

const char *__kea_io_read_file(const char *path) {
  if (path == NULL) {
    return KEA_EMPTY_STRING;
  }

  FILE *file = fopen(path, "rb");
  if (file == NULL) {
    return KEA_EMPTY_STRING;
  }

  if (fseek(file, 0, SEEK_END) != 0) {
    fclose(file);
    return KEA_EMPTY_STRING;
  }

  long size = ftell(file);
  if (size < 0) {
    fclose(file);
    return KEA_EMPTY_STRING;
  }
  rewind(file);

  char *buffer = (char *)malloc((size_t)size + 1);
  if (buffer == NULL) {
    fclose(file);
    return KEA_EMPTY_STRING;
  }

  size_t read = fread(buffer, 1, (size_t)size, file);
  fclose(file);
  buffer[read] = '\0';
  return buffer;
}

#ifndef _WIN32
static int split_host_port(const char *addr, char *host, size_t host_len,
                           const char **port) {
  const char *colon = strrchr(addr, ':');
  if (colon == NULL || colon == addr || *(colon + 1) == '\0') {
    return -1;
  }

  size_t host_part_len = (size_t)(colon - addr);
  if (host_part_len >= host_len) {
    return -1;
  }

  memcpy(host, addr, host_part_len);
  host[host_part_len] = '\0';
  *port = colon + 1;
  return 0;
}
#endif

int64_t __kea_net_connect(const char *addr) {
#ifdef _WIN32
  (void)addr;
  return -1;
#else
  if (addr == NULL) {
    return -1;
  }

  char host[256];
  const char *port = NULL;
  if (split_host_port(addr, host, sizeof(host), &port) != 0) {
    return -1;
  }

  struct addrinfo hints;
  memset(&hints, 0, sizeof(hints));
  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;

  struct addrinfo *results = NULL;
  if (getaddrinfo(host, port, &hints, &results) != 0) {
    return -1;
  }

  int socket_fd = -1;
  for (struct addrinfo *candidate = results; candidate != NULL;
       candidate = candidate->ai_next) {
    socket_fd = socket(candidate->ai_family, candidate->ai_socktype,
                       candidate->ai_protocol);
    if (socket_fd < 0) {
      continue;
    }
    if (connect(socket_fd, candidate->ai_addr, candidate->ai_addrlen) == 0) {
      break;
    }
    close(socket_fd);
    socket_fd = -1;
  }

  freeaddrinfo(results);
  return socket_fd < 0 ? -1 : (int64_t)socket_fd;
#endif
}

int8_t __kea_net_send(int64_t conn, const char *data) {
#ifdef _WIN32
  (void)conn;
  (void)data;
  return -1;
#else
  if (conn < 0 || data == NULL) {
    return -1;
  }
  size_t len = strlen(data);
  ssize_t sent = send((int)conn, data, len, 0);
  return sent == (ssize_t)len ? 0 : -1;
#endif
}

int64_t __kea_net_recv(int64_t conn, int64_t size) {
#ifdef _WIN32
  (void)conn;
  (void)size;
  return -1;
#else
  if (conn < 0 || size <= 0) {
    return 0;
  }

  char *buffer = (char *)malloc((size_t)size);
  if (buffer == NULL) {
    return -1;
  }

  ssize_t received = recv((int)conn, buffer, (size_t)size, 0);
  free(buffer);
  return received < 0 ? -1 : (int64_t)received;
#endif
}

const char *__kea_float_to_string(double f) {
  /* Use a 64-byte buffer — sufficient for any IEEE 754 double representation. */
  char *buf = (char *)malloc(64);
  if (buf == NULL) return KEA_EMPTY_STRING;
  snprintf(buf, 64, "%g", f);
  return buf;
}

const char *__kea_string_from_c_str(const char *ptr) {
  if (ptr == NULL) return KEA_EMPTY_STRING;
  size_t len = strlen(ptr);
  char *buf = (char *)malloc(len + 1);
  if (buf == NULL) return KEA_EMPTY_STRING;
  memcpy(buf, ptr, len);
  buf[len] = '\0';
  return buf;
}

int64_t __kea_sys_malloc(int64_t size) {
  if (size <= 0) return 0;
  return (int64_t)malloc((size_t)size);
}

void __kea_sys_free(int64_t ptr) {
  if (ptr != 0) free((void *)ptr);
}

void __kea_panic_div_zero(void) {
  static const char msg[] = "panic: integer division by zero\n";
  fwrite(msg, 1, sizeof(msg) - 1, stderr);
  fflush(stderr);
  _exit(101);
}

void __kea_panic_mod_zero(void) {
  static const char msg[] = "panic: integer remainder by zero\n";
  fwrite(msg, 1, sizeof(msg) - 1, stderr);
  fflush(stderr);
  _exit(101);
}

int64_t __kea_clock_now(void) {
#ifdef _WIN32
  return -1;
#else
  struct timespec ts;
  if (clock_gettime(CLOCK_REALTIME, &ts) != 0) {
    return -1;
  }
  return (int64_t)ts.tv_sec * 1000000000LL + (int64_t)ts.tv_nsec;
#endif
}

int64_t __kea_clock_monotonic(void) {
#ifdef _WIN32
  return -1;
#else
  struct timespec ts;
  if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) {
    return -1;
  }
  return (int64_t)ts.tv_sec * 1000000000LL + (int64_t)ts.tv_nsec;
#endif
}

// Test assertion stubs: used when Test module is imported by library code
// (e.g. stdlib/vector.kea imports Test) but the compiled binary is not a
// test runner.  A failing assertion aborts the process; passing ones are
// silent.
void __kea_test_check(int8_t passed) {
  if (!passed) {
    fputs("assertion failed\n", stderr);
    abort();
  }
}

void __kea_test_check_with_message(int8_t passed, const char *msg) {
  if (!passed) {
    fprintf(stderr, "assertion failed: %s\n", msg ? msg : "(null)");
    abort();
  }
}

// TLS fail-propagation slot: out-of-band channel for Fail payloads that
// cannot propagate through the pure handler callback ABI.
static __thread const uint8_t *__kea_fail_payload_slot = NULL;

const uint8_t *__kea_get_fail_payload(void) { return __kea_fail_payload_slot; }
void __kea_set_fail_payload(const uint8_t *p) { __kea_fail_payload_slot = p; }
const uint8_t *__kea_take_fail_payload(void) {
  const uint8_t *p = __kea_fail_payload_slot;
  __kea_fail_payload_slot = NULL;
  return p;
}
