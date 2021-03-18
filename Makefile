all:
	pdflatex main
	-bibtex main
	-pdflatex main
	-pdflatex main
ifeq ($(USER),bcpierce)
	-cp -f ~/common/bib/bcp.bib .
	chmod a-w bcp.bib
endif

coq:
	coqc -R . "" Trace.v
	coqc -R . "" Machine.v
	coqc -R . "" ObsTrace.v

clean:
	rm -f *.aux *.vio *.vo* *.glob
