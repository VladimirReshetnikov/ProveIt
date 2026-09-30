PYTHON ?= python3
LATEX ?= pdflatex

.PHONY: pdf verify clean
pdf:
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex

# ProveIt edit (2026-09-29): verify.py now writes data/run_summary.txt itself,
# after a successful run; the shell redirection truncated it on a failed run.
verify:
	$(PYTHON) code/verify.py --max-n 4096

clean:
	rm -f article.aux article.log article.out article.toc
