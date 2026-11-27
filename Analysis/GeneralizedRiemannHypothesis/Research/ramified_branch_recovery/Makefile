.PHONY: verify independent figures pdf

verify:
	python3 code/verify.py

independent:
	python3 code/independent_jet_check.py
	python3 code/independent_tree_check.py
	python3 code/independent_nonpacking_check.py

figures:
	python3 code/make_figures.py

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error paper.tex
	pdflatex -interaction=nonstopmode -halt-on-error paper.tex
