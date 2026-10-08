.PHONY: all assets clean

all:
	latexmk -pdf -interaction=nonstopmode -halt-on-error unknot_modular_boundary.tex

assets:
	python3 -B build_assets.py

clean:
	latexmk -c unknot_modular_boundary.tex
