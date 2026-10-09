MAIN = unknot_singleton_dag

.PHONY: all clean
all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex references.bib $(wildcard sections/*.tex) $(wildcard generated/*.tex) figures/stage_scaling.pdf
	pdflatex -interaction=nonstopmode -halt-on-error $(MAIN).tex
	bibtex $(MAIN)
	pdflatex -interaction=nonstopmode -halt-on-error $(MAIN).tex
	pdflatex -interaction=nonstopmode -halt-on-error $(MAIN).tex

clean:
	rm -f $(MAIN).aux $(MAIN).bbl $(MAIN).blg $(MAIN).log $(MAIN).out $(MAIN).toc
