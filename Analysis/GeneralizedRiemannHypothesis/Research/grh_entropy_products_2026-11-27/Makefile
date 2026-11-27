.PHONY: all check clean
all: entropy_products.pdf check
entropy_products.pdf: entropy_products.tex
	pdflatex -interaction=nonstopmode -halt-on-error entropy_products.tex
	pdflatex -interaction=nonstopmode -halt-on-error entropy_products.tex
check:
	python3 check_finite.py > finite_checks.json
clean:
	rm -f entropy_products.aux entropy_products.log entropy_products.out
