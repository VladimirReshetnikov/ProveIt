.PHONY: all verify pdf clean
all: verify pdf
verify:
	python3 verify.py | tee verification.txt
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error paper.tex
	pdflatex -interaction=nonstopmode -halt-on-error paper.tex
clean:
	rm -f paper.aux paper.log paper.out
