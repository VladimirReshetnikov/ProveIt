.PHONY: pdf check lean

pdf:
	cd paper && pdflatex -interaction=nonstopmode -halt-on-error ipra_stable_observables.tex
	cd paper && pdflatex -interaction=nonstopmode -halt-on-error ipra_stable_observables.tex

check:
	python3 code/verify_spectral.py
	python3 code/verify_observables.py

lean:
	cd lean && bash build.sh
