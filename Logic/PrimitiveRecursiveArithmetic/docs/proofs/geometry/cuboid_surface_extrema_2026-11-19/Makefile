.PHONY: pdf figures check symbolic

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error cuboid_surface.tex

figures:
	python3 code/make_figures.py

check:
	python3 code/validate.py

symbolic:
	python3 code/verify_algebra.py
