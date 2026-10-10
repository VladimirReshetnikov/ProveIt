.PHONY: all pdf verify verify-independent numerics regenerate clean
all: pdf
pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
verify:
	python code/verify_exact.py
	python -O code/verify_exact.py
verify-independent:
	python code/verify_sympy.py
numerics:
	python code/numerical_checks.py
regenerate:
	python code/generate_certificates.py
	python code/verify_exact.py
clean:
	latexmk -c article.tex
