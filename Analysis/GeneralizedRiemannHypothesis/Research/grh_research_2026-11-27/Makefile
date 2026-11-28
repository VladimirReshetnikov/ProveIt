.PHONY: all papers verify clean

all: papers verify

papers:
	cd papers && latexmk -pdf -interaction=nonstopmode -halt-on-error sparse_roots.tex
	cd papers && latexmk -pdf -interaction=nonstopmode -halt-on-error torsion_phase_transition.tex

verify:
	python3 code/run_checks.py

clean:
	cd papers && latexmk -c sparse_roots.tex torsion_phase_transition.tex
