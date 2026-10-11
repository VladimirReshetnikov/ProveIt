PYTHON ?= python3
.PHONY: all pdf check clean
all: pdf check
pdf:
	cd manuscript && pdflatex -interaction=nonstopmode -halt-on-error article.tex
	cd manuscript && pdflatex -interaction=nonstopmode -halt-on-error article.tex
check:
	$(PYTHON) code/verify_exact.py > data/exact_checks.txt
	$(PYTHON) code/verify_numeric.py > data/numeric_checks.txt
clean:
	rm -f manuscript/article.aux manuscript/article.log manuscript/article.out manuscript/article.toc manuscript/article.fls manuscript/article.fdb_latexmk
	rm -rf code/__pycache__
