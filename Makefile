all: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

Makefile.coq:
	rocq makefile -f _CoqProject -o Makefile.coq

autosubst:
	autosubst -f -s urocq -v ge813 -p ./theories/autosubst/AST_preamble.v -o ./theories/autosubst/AST.v ./theories/autosubst/AST.sig

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean autosubst


doc:
	$(MAKE) coqdoc
	sed -i 's/doc\/\([^\/]*\)\/stdlib/doc\/\1\/corelib/g' doc/coqdoc/*
	pandoc --standalone --output=index.html --css=doc/github-pandoc.css --metadata title="Acc in SProp" README.md

.PHONY: doc
