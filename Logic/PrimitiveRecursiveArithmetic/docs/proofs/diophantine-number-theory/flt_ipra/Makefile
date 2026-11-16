.PHONY: pdf check clean

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error flt_ipra.tex
	pdflatex -interaction=nonstopmode -halt-on-error flt_ipra.tex
	pdflatex -interaction=nonstopmode -halt-on-error flt_ipra.tex

check:
	python3 code/verify_cubic.py
	python3 code/verify_quintic.py
	python3 code/verify_seven.py
	python3 code/coverage.py --limit 200 --csv evidence/exponents_through_200.csv --json evidence/coverage.json

clean:
	rm -f flt_ipra.aux flt_ipra.log flt_ipra.out flt_ipra.toc
