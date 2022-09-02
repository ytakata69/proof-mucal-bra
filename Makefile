targets = automata.vo
srcs = ltl.v automata.v
docdir = ./docs
vobjs = $(srcs:.v=.vo)

.PHONY: default all doc clean distclean
%.vo: %.v
	coqc $<

default: $(targets)
all: $(targets)

automata.vo: ltl.vo

doc: $(vobjs)
	test -d $(docdir) || mkdir $(docdir)
	coqdoc --gallina --utf8 -d $(docdir) $(srcs)

clean:
	$(RM) *.vo *.vo[ks] *.glob .*.aux *~

distclean: clean
	$(RM) $(docdir)/*.{html,css}
