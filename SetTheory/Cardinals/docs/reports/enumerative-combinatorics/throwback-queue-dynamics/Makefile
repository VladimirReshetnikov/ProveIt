.PHONY: all pdf check clean
all: pdf
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error throwback_research.tex
	pdflatex -interaction=nonstopmode -halt-on-error throwback_research.tex
check:
	python3 code/verify.py
	python3 code/extra_results.py
clean:
	rm -f throwback_research.aux throwback_research.log throwback_research.out throwback_research.toc throwback_research.fdb_latexmk throwback_research.fls
