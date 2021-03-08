NAME	:= $(shell basename `pwd`)

all: run

run: $(NAME).ss libdemo.so
	scheme $<

demo: libdemo.so

libdemo.so: demo.c
	gcc -shared -fPIC -Os -s $< -o$@

edit:
	vim -c 'set nu et fdm=marker bg=dark' $(NAME).ss

.PHONY: all run demo edit
