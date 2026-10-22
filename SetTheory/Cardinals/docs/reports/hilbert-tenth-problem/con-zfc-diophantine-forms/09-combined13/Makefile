.PHONY: verify pdf clean
verify:
	python3 verify_arithmetic.py
	python3 verify_compiler.py

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error con_zfc_reductions.tex

clean:
	latexmk -c con_zfc_reductions.tex

