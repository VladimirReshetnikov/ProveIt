.PHONY: verify paper figure lean clean

verify:
	python3 code/exact_models.py --output certificates/certificates.json

paper:
	latexmk -cd -pdf -interaction=nonstopmode -halt-on-error paper/platonic_solids_ipra.tex

figure:
	python3 code/draw_models.py

lean:
	cd lean && lake build Arithmetic

clean:
	latexmk -cd -c paper/platonic_solids_ipra.tex
