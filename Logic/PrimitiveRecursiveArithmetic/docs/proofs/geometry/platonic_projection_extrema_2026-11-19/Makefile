.PHONY: verify figures pdf

verify:
	python3 code/exact_verify.py --output certificates
	python3 code/icosahedron_independent.py > certificates/icosahedron_independent.json

figures:
	python3 code/draw_shadows.py

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
