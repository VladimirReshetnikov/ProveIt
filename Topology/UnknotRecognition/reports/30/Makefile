.PHONY: pdf verify verify-full clean

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error unknot_binary_tensors.tex

verify:
	python3 -B verify.py

verify-full:
	python3 -B verify.py --full

clean:
	latexmk -c unknot_binary_tensors.tex
