#include<signal.h>
#include<stdio.h>
#include<termios.h>
#include<unistd.h>

#define UNBLOCK(_S) do {\
	sigset_t mask;\
	sigemptyset(&mask);\
	sigaddset(&mask, _S);\
	sigprocmask(SIG_UNBLOCK, &mask, NULL);\
} while (0)

#define CALL_HAND(_H, _S, _HN) do {\
	if ((_H) == SIG_DFL) {\
		signal(_S, SIG_DFL);\
		raise(_S);\
		signal(_S, _HN);\
	} else if ((_H) != SIG_IGN) {\
		(_H)(_S);\
	}\
} while (0)

static void (*old_handler[6])(int);
void demo_exit(void);

static void term_setup(void)
{
	struct termios term_in;
	tcgetattr(STDIN_FILENO, &term_in);
	term_in.c_lflag &= (~ICANON & ~ECHO);
	tcsetattr(STDIN_FILENO, TCSANOW, &term_in);
	puts("\x1b[2J\x1b[?25l");
	fflush(stdout);
}

static void term_cleanup(void)
{
	struct termios term_in;
	puts("\x1b[?25h");
	fflush(stdout);
	tcgetattr(STDIN_FILENO, &term_in);
	term_in.c_lflag |= (ICANON | ECHO);
	tcsetattr(STDIN_FILENO, TCSANOW, &term_in);
}

static void sigexit(int sig)
{
	UNBLOCK(sig);
	demo_exit();
	raise(sig);
}

static void sigtstp(int sig)
{
	UNBLOCK(SIGTSTP);
	term_cleanup();
	CALL_HAND(old_handler[0], SIGTSTP, sigtstp);
}

static void sigcont(int sig)
{
	UNBLOCK(SIGCONT);
	term_setup();
	CALL_HAND(old_handler[1], SIGCONT, sigcont);
}

static void sigint(int sig)
{
	UNBLOCK(SIGINT);
	demo_exit();
	raise(SIGINT);
}

void demo_init(void)
{
	old_handler[0] = signal(SIGTSTP, sigtstp);
	old_handler[1] = signal(SIGCONT, sigcont);
	old_handler[2] = signal(SIGINT, sigint);
	old_handler[3] = signal(SIGHUP, sigexit);
	old_handler[4] = signal(SIGQUIT, sigexit);
	old_handler[5] = signal(SIGTERM, sigexit);
	term_setup();
}

void demo_exit(void)
{
	term_cleanup();
	signal(SIGTSTP, old_handler[0]);
	signal(SIGCONT, old_handler[1]);
	signal(SIGINT, old_handler[2]);
	signal(SIGHUP, old_handler[3]);
	signal(SIGQUIT, old_handler[4]);
	signal(SIGTERM, old_handler[5]);
}
