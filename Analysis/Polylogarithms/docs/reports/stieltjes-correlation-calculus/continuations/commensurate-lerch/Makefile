PYTHON ?= python3
NAME = ProveIt_Commensurate_Lerch_Calculus_2026-10-10
.PHONY: all verify pdf clean
all: verify pdf
verify:
	$(PYTHON) code/verify.py --part exact
	$(PYTHON) code/verify.py --part numeric
	$(PYTHON) code/verify_extra.py
	$(PYTHON) code/summarize_verification.py
pdf:
	$(PYTHON) code/make_standalone.py
	pdflatex -interaction=nonstopmode -halt-on-error $(NAME).tex
	pdflatex -interaction=nonstopmode -halt-on-error $(NAME).tex
	pdflatex -interaction=nonstopmode -halt-on-error $(NAME).tex
clean:
	rm -f *.aux *.log *.out *.toc *.fls *.fdb_latexmk
