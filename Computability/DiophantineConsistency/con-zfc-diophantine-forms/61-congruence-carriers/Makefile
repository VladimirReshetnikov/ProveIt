.PHONY: all verify pdf clean

all: verify pdf

verify:
	python3 verify_all.py

pdf:
	cd report && latexmk -pdf -interaction=nonstopmode -halt-on-error congruence_carriers.tex

clean:
	cd report && latexmk -c congruence_carriers.tex
