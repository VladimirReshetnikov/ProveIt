.PHONY: all pdf check clean

all: check pdf

check:
	python3 certificates/verify_certificates.py > certificates/verification_stdout.txt

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

clean:
	latexmk -C main.tex
	rm -f main.bbl main.run.xml
