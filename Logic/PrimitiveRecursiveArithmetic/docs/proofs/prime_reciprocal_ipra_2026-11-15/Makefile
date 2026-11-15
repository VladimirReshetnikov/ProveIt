.PHONY: all pdf check clean

all: check pdf

check:
	python3 scripts/check_finite_lemmas.py

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error prime_reciprocal_ipra.tex

clean:
	latexmk -C prime_reciprocal_ipra.tex
	rm -f artifacts/verification_report.txt
