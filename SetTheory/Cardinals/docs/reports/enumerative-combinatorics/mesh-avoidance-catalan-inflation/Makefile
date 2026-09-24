PYTHON ?= python3

.PHONY: all pdf check check-records cross symbolic clean

all: pdf check check-records cross

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
	latexmk -c

check:
	$(PYTHON) code/verify.py

check-records:
	$(PYTHON) code/verify_records.py --max-n 1000 --exhaustive 11

cross:
	$(PYTHON) code/cross_check.py

symbolic:
	$(PYTHON) code/symbolic_checks.py
	$(PYTHON) code/symbolic_check_records.py

clean:
	rm -f article.aux article.log article.out article.toc \
	      article.fdb_latexmk article.fls
	rm -rf code/__pycache__
