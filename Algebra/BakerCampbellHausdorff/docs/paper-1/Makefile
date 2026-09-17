.PHONY: all pdf verify clean

all: pdf

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error bch_complete.tex

verify:
	python3 code/verify_bch.py --degree 10 --output data > data/verification_log.txt
	cat data/verification_log.txt

clean:
	latexmk -c bch_complete.tex
