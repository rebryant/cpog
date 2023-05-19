CC=gcc
CXX=g++
OPT=-O2
#OPT=-O0
CFLAGS=-g $(OPT) -Wno-nullability-completeness
CPPFLAGS=-g $(OPT) -Wno-nullability-completeness -std=c++11

install: all

all: cpog-check cpog-gen


cpog-check: cpog-check.c q25.c q25.h
	$(CC) $(CFLAGS) cpog-check.c q25.c -o cpog-check

ilist.o: ilist.c ilist.h
	$(CC) $(CFLAGS) -c ilist.c

report.o: report.c report.h
	$(CC) $(CFLAGS) -c report.c

counters.o: counters.c counters.h
	$(CC) $(CFLAGS) -c counters.c

clausal.o: ilist.h counters.h clausal.hh writer.hh clausal.cpp
	$(CXX) $(CPPFLAGS) -c clausal.cpp

writer.o: ilist.h report.h writer.hh writer.cpp
	$(CXX) $(CPPFLAGS) -c writer.cpp

pog.o: pog.hh clausal.hh counters.h pog.cpp
	$(CXX) $(CPPFLAGS) -c pog.cpp

cpog-gen: cpog-gen.cpp clausal.o ilist.o report.o counters.o writer.o pog.o
	$(CXX) $(CPPFLAGS) -o cpog-gen cpog-gen.cpp clausal.o ilist.o report.o counters.o writer.o pog.o

.SUFFIXES: .c .cpp .o

.c.o:
	$(CC) $(CFLAGS) $(INC) -c $<

.cpp.o:
	$(CXX) $(CPPFLAGS) $(INC) -c $<

clean:
	rm -f *.o *~
	rm -rf *.dSYM

superclean: clean
	rm -f cpog-gen cpog-check


