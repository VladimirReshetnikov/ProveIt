.PHONY: all pdf verify numerics clean

all: verify pdf

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error stern_conjecture_note.tex
	pdflatex -interaction=nonstopmode -halt-on-error stern_conjecture_note.tex

verify:
	python3 code/verify_exact.py

numerics:
	python3 code/numerical_checks.py

clean:
	rm -f stern_conjecture_note.aux stern_conjecture_note.log stern_conjecture_note.out
