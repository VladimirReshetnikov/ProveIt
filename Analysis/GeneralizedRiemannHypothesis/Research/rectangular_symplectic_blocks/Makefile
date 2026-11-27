.PHONY: all paper verify figure clean

all: paper

paper:
	latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex

verify:
	python3 code/exact_laws.py
	python3 code/joint_laws.py
	python3 code/independent_enumeration.py
	python3 code/verify_independent.py

figure:
	python3 code/make_figure.py

clean:
	latexmk -c paper.tex
