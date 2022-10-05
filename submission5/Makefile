all:
	pdflatex noexceptions
	-bibtex noexceptions
	-pdflatex noexceptions
	-pdflatex noexceptions
ifeq ($(USER),bcpierce)
	-cp -f ~/common/bib/bcp.bib .
	chmod a-w bcp.bib
endif

clean:
	rm -f *.aux *.blg *.out *.bbl *.pdf *.log
