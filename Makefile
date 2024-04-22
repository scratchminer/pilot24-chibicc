CFLAGS=-std=c11 -g -Wall

SRCS=$(wildcard *.c)
OBJS=$(SRCS:.c=.o)

all: chibicc

chibicc: $(OBJS)
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

$(OBJS): chibicc.h

clean:
	rm -rf chibicc
	find * -type f '(' -name '*~' -o -name '*.o' ')' -exec rm {} ';'

.PHONY: all clean
