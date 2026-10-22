.PHONY: verify pdf

verify:
	python3 verify.py

pdf:
	cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error fixed_input_zfc.tex
