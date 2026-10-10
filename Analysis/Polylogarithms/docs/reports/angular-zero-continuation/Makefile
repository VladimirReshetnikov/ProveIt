.PHONY: all verify figures clean

all: article.pdf

article.pdf: article.tex figures/angular_geometry.pdf figures/normalized_radius_conjecture.pdf
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

verify:
	python3 code/run_verification.py

figures:
	python3 figures/generate_figures.py

clean:
	latexmk -c article.tex
