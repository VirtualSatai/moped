# Cudd stuff:
CUDDVER = cudd-2.5.1
CUDDINCLUDEDIR=../$(CUDDVER)/include
CUDDLIBDIR=../$(CUDDVER)/lib
CUDDLIBS=cudd mtr st util epd

# Windows / Posix differences:
ifdef WIN32
  MOPED = moped.exe
  CC = cl /MT /I$(CUDDINCLUDEDIR) /DWIN32
  LINK=link
  LIBS = /libpath:"$(CUDDLIBDIR)" $(patsubst %,lib%.lib,$(CUDDLIBS))
  O = obj
else # POSIX
  MOPED = moped
  CCINCLUDEDIR = ""
  CC = gcc -g -O3 -Wall -I$(CUDDINCLUDEDIR) #-DYYDEBUG
  LINK=$(CC)
  LIBS =  -L$(CUDDLIBDIR) $(patsubst %,-l%,$(CUDDLIBS)) -lm
  O = o
endif

TMPFILES = baparse.c balex.c pdsparse.c pdslex.c \
	   bp.c bplex.c ltlparse.c ltllex.c prop.c proplex.c

MODULES = ba baparse common fatrans ftree heads main mcheck \
	  name pds pdsparse poststar prestar prereach reorder bdd \
	  graph elim closure xb el cycle bktrace fwtrace trace \
	  bp bptree bpmake bpgraph bptrace bpuse sort netconv \
	  pa ltlparse prop expr

OBJECTS = $(MODULES:=.$(O))

$(MOPED): $(OBJECTS)
ifdef WIN32
	$(LINK) $(OBJECTS) /OUT:$@ $(LIBS)
else # POSIX
	$(LINK) $(OBJECTS) -o $@ $(LIBS)
endif

# Compiling:
%.$(O): %.c
	$(CC) -c $<

# miscellaneous parsers

baparse.$(O): baparse.c balex.c
baparse.c: baparse.y
	bison baparse.y -p ba -o $@
balex.c: balex.l
	flex -o$@ -Pba balex.l

pdsparse.$(O): pdsparse.c pdslex.c
pdsparse.c: pdsparse.y
	bison pdsparse.y -p pds -o $@
pdslex.c: pdslex.l
	flex -o$@ -Ppds pdslex.l

bp.$(O): bp.c bplex.c
bp.c: bp.y
	bison bp.y -p bp -o $@
bplex.c: bplex.l
	flex -o$@ -Pbp bplex.l

ltlparse.$(O): ltlparse.c ltllex.c
ltlparse.c: ltlparse.y ltllex.c
	bison ltlparse.y -p ltl -o $@
ltllex.c: ltllex.l
	flex -t -Pltl ltllex.l | \
	sed 's/getc( ltlin )) != EOF/*ltlstr) \&\& (ltlstr += !!*ltlstr)/g' > $@

prop.$(O): prop.c proplex.c
prop.c: prop.y proplex.c
	bison prop.y -p prop -o $@
proplex.c: proplex.l
	flex -t -Pprop proplex.l | \
	sed 's/getc( propin )) != EOF/*propstr) \&\& (propstr += !!*propstr)/g'>$@

# clean

clean: 
	rm -f $(MOPED) $(OBJECTS) $(TMPFILES) \
              frag_* core* *.$(O) *.output mon.out gmon.out *.d .deps

# Dependencies

%.d: %.c
ifdef WIN32
	mkdep -n $? > $@
else # POSIX
	$(SHELL) -ec '$(CC) -MM $? | sed '\''s/$*.o/& $@/g'\'' > $@'
endif

DEPS = $(OBJECTS:%.$(O)=%.d)

.deps: $(DEPS)
	echo " " $(DEPS) | \
	sed 's/[ 	][ 	]*/#include /g' | tr '#' '\012' > .deps

include .deps

