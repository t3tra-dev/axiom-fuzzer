/* Lifeline of a forked portfolio child (POSIX: macOS and Linux).

   The supervisor holds the only write end of a pipe that it never writes to. A child keeps
   the read end and, from here on, a small detached pthread blocked in read(2) on it. When the
   supervisor dies, however it dies (SIGKILL, abort, a fatal runtime error), the kernel closes
   its descriptors and the read returns 0. The thread then ends the child, independently of
   what the child's OCaml code is doing: no polling, no OCaml runtime call, no allocation.

   [grace_ms] = 0: SIGKILL at once. [grace_ms] > 0: SIGTERM first (the child's own handler
   turns it into a cooperative stop, which lets the reference save its checkpoint), then
   SIGKILL after [grace_ms] if the child is still alive. SIGKILL goes to the child's process
   group when the child leads one (it calls setsid right after the fork), so anything it
   started dies with it; otherwise to the child alone, never to a group it does not lead.

   The thread is created with every signal blocked, so asynchronous signals keep going to the
   OCaml thread, and it never touches the OCaml heap. It does not survive a fork (the child
   never forks), and Unix._exit ends it with the process. */

#include <errno.h>
#include <pthread.h>
#include <signal.h>
#include <time.h>
#include <unistd.h>
#include <caml/fail.h>
#include <caml/mlvalues.h>

struct axiom_lifeline {
  int fd;
  long grace_ms;
};

static struct axiom_lifeline axiom_lifeline_state;

static void axiom_lifeline_kill(int signal) {
  if (getpgrp() == getpid())
    (void)kill(0, signal);
  else
    (void)kill(getpid(), signal);
}

static void *axiom_lifeline_main(void *arg) {
  struct axiom_lifeline *l = arg;
  char buffer[64];
  for (;;) {
    ssize_t n = read(l->fd, buffer, sizeof buffer);
    if (n == 0) break;                   /* every write end is closed */
    if (n < 0 && errno != EINTR) break;  /* the pipe is unusable: treat it as closed */
    /* n > 0: nobody writes to the lifeline; ignore stray bytes and keep waiting. */
  }
  if (l->grace_ms > 0) {
    (void)kill(getpid(), SIGTERM);
    struct timespec step = {0, 10 * 1000 * 1000};
    for (long waited = 0; waited < l->grace_ms; waited += 10) (void)nanosleep(&step, NULL);
  }
  axiom_lifeline_kill(SIGKILL);
  _exit(3);
  return NULL;
}

CAMLprim value axiom_lifeline_start(value fd, value grace_ms) {
  sigset_t all, old;
  pthread_attr_t attr;
  pthread_t thread;
  int rc;
  axiom_lifeline_state.fd = Int_val(fd);
  axiom_lifeline_state.grace_ms = Long_val(grace_ms) < 0 ? 0 : Long_val(grace_ms);
  sigfillset(&all);
  if (pthread_sigmask(SIG_SETMASK, &all, &old) != 0) caml_failwith("lifeline: pthread_sigmask");
  rc = pthread_attr_init(&attr);
  if (rc == 0) {
    (void)pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);
    (void)pthread_attr_setstacksize(&attr, 64 * 1024);
    rc = pthread_create(&thread, &attr, axiom_lifeline_main, &axiom_lifeline_state);
    (void)pthread_attr_destroy(&attr);
  }
  (void)pthread_sigmask(SIG_SETMASK, &old, NULL);
  if (rc != 0) caml_failwith("lifeline: pthread_create");
  return Val_unit;
}
