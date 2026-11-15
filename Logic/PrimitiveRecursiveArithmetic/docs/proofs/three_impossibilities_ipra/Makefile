.PHONY: all pdf checks clean

all: pdf checks

pdf:
	mkdir -p build
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build three_classical_impossibilities_ipra.tex
	cp build/three_classical_impossibilities_ipra.pdf ./three_classical_impossibilities_ipra.pdf

checks:
	mkdir -p evidence
	python3 scripts/finite_checks.py | tee evidence/finite_checks.txt

clean:
	latexmk -C -outdir=build three_classical_impossibilities_ipra.tex || true
	rm -rf build rendered contact_*.png
