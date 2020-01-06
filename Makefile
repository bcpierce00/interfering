all:
	pdflatex main
	bibtex main
	pdflatex main
	pdflatex main
ifeq ($(USER),bcpierce)
	-cp -f ~/common/bib/bcp.bib .
	chmod a-r bcp.bib
endif
