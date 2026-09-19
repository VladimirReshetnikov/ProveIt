.PHONY: all verify quick clean
all: report.pdf
report.pdf: report.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
verify:
	python3 verify.py --full --out verification_results.json
quick:
	python3 verify.py
clean:
	latexmk -c report.tex
