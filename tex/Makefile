all:
	pdflatex main
	-bibtex main
	-pdflatex main
	-pdflatex main
ifeq ($(USER),bcpierce)
	-cp -f ~/common/bib/bcp.bib .
	chmod a-w bcp.bib
endif

clean:
	rm -f *.aux *.blg *.out *.bbl *.pdf *.log
