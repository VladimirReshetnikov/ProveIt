.PHONY: all verify positive clean
all: report.pdf

report.pdf: report.tex positive/section.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

verify:
	python3 reproduce.py

positive:
	python3 positive/check_majorant.py

clean:
	latexmk -c report.tex
