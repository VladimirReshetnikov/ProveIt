.PHONY: all verify pdf clean

all: verify pdf

verify:
	python3 code/verify_pentagonal_tilings.py | tee verification/run_stdout.json

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error pentagonal_tiling_ipra.tex > verification/latexmk_stdout.txt 2>&1
	pdfinfo pentagonal_tiling_ipra.pdf > verification/pdfinfo.txt
	pdftotext pentagonal_tiling_ipra.pdf verification/pentagonal_tiling_ipra.txt

clean:
	latexmk -c pentagonal_tiling_ipra.tex
	rm -rf code/__pycache__
