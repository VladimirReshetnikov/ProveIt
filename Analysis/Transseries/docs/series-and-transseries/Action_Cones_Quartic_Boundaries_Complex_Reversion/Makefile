.PHONY: pdf verify clean

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error complex_transseries_reversion.tex

verify:
	python verification/verification.py
	python verification/quartic_saddle_checks.py

clean:
	latexmk -c complex_transseries_reversion.tex

