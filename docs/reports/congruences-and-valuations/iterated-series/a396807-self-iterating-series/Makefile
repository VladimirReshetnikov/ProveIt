.PHONY: all report check symbolic clean

all: report check

report:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

check:
	python code/verify.py

symbolic:
	python code/symbolic_checks.py

clean:
	latexmk -c article.tex
