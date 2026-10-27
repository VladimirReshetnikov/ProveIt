.PHONY: all pdf check integrity

all: pdf check

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

check:
	python3 code/run_checks.py

integrity:
	python3 code/verify_manifest.py
