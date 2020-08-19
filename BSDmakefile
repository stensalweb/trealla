GIT_VERSION := "$(shell git describe --abbrev=4 --dirty --always --tags)"
CFLAGS = -Isrc -I/usr/local/include -DUSE_SSL=$(USE_SSL) -DVERSION='$(GIT_VERSION)' -O3 $(OPT) -Wall -D_GNU_SOURCE
LDFLAGS = -L/usr/local/lib -lm

.ifndef NOSSL
USE_SSL = 1
LDFLAGS += -lssl -lcrypto
.else
USE_SSL = 0
.endif

OBJECTS = tpl.o history.o builtins.o library.o \
	parse.o print.o runtime.o \
	skiplist.o base64.o network.o utf8.o\
	lists.o dict.o apply.o http.o auth.o

PL = ./tpl

all: tpl

tpl: $(OBJECTS)
	$(CC) -o tpl $(OBJECTS) $(OPT) $(LDFLAGS)

nossl:
	$(MAKE) 'OPT=$(OPT) -DUSE_SSL=0' NOSSL=0

profile:
	$(MAKE) 'OPT=$(OPT) -O0 -pg -DDEBUG'

debug:
	$(MAKE) 'OPT=$(OPT) -O0 -g -DDEBUG'

debug128:
	$(MAKE) 'OPT=$(OPT) -O0 -g -DDEBUG -DUSE_INT128=1'

int128:
	$(MAKE) 'OPT=$(OPT) -DUSE_INT128=1'

nossl128:
	$(MAKE) 'OPT=$(OPT) -DUSE_SSL=0 -DUSE_INT128=1' NOSSL=0

test:
	./tests/run.sh

valgrind:
	./tests/run_valgrind.sh

testswi:
	./tests/runswi.sh

clean:
	rm -f tpl *.o *.out gmon.* *.core

# from [gcc|clang] -MM *.c

base64.o: base64.c base64.h
builtins.o: builtins.c builtins.h parse.h internal.h skiplist.h network.h base64.h \
 utf8.h
history.o: history.c history.h utf8.h
library.o: library.c library.h
network.o: network.c internal.h skiplist.h network.h
parse.o: parse.c internal.h skiplist.h library.h parse.h utf8.h
print.o: print.c internal.h skiplist.h utf8.h
runtime.o: runtime.c internal.h skiplist.h
skiplist.o: skiplist.c skiplist.h
tpl.o: tpl.c history.h parse.h
utf8.o: utf8.c utf8.h

# Library modules

dict.o: library/dict.pro
	$(LD) -m elf_x86_64 -r -b binary -o dict.o library/dict.pro

lists.o: library/lists.pro
	$(LD) -m elf_x86_64 -r -b binary -o lists.o library/lists.pro

apply.o: library/apply.pro
	$(LD) -m elf_x86_64 -r -b binary -o apply.o library/apply.pro

http.o: library/http.pro
	$(LD) -m elf_x86_64 -r -b binary -o http.o library/http.pro

auth.o: library/auth.pro
	$(LD) -r -b binary -o auth.o library/auth.pro
