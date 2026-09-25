all: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq:
	rocq makefile -f _CoqProject -o Makefile.coq

autosubst:
	autosubst -f -s urocq -v ge813 -p ./Syntax/Preamble.v -o ./Syntax/Syntax.v ./Syntax/cicm.sig

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean autosubst
