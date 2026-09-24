.PHONY: all check clean
all: ordinal_separation.pdf
ordinal_separation.pdf: ordinal_separation.tex
	pdflatex -interaction=nonstopmode -halt-on-error ordinal_separation.tex
	pdflatex -interaction=nonstopmode -halt-on-error ordinal_separation.tex
check:
	python3 code/finite_checks.py --output verification/results.json
clean:
	rm -f ordinal_separation.aux ordinal_separation.log ordinal_separation.out ordinal_separation.toc
