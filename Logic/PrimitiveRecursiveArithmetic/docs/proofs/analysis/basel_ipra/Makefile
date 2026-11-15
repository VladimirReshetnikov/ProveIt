.PHONY: pdf check clean

pdf:
	cd paper && pdflatex -interaction=nonstopmode -halt-on-error basel_ipra.tex
	cd paper && pdflatex -interaction=nonstopmode -halt-on-error basel_ipra.tex

check:
	python3 code/check_bounds.py --output validation/exact_checks.json
	python3 code/check_quadrature.py --output validation/quadrature_checks.json
	python3 code/check_encodings.py --output validation/encoding_checks.json

clean:
	rm -f paper/basel_ipra.aux paper/basel_ipra.log paper/basel_ipra.out paper/basel_ipra.toc
