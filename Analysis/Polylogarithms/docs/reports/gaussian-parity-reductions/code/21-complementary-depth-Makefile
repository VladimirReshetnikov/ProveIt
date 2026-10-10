PYTHON ?= python3
LATEXMK ?= latexmk

.PHONY: all pdf test clean
all: test pdf

pdf:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error article.tex

test:
	$(PYTHON) code/check_exact.py
	$(PYTHON) code/check_numerical.py
	$(PYTHON) code/certify_gaussian.py
	$(PYTHON) code/audit_s4_rows.py
	$(PYTHON) code/replay_certificates.py

clean:
	$(LATEXMK) -c article.tex
