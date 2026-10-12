.PHONY: pdf exact numeric explore clean

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

exact:
	python verification/verify_exact.py
	python verification/verify_endpoints.py

numeric:
	python verification/verify_numeric.py

explore:
	python verification/exploratory_all_orders.py

clean:
	latexmk -c article.tex
	rm -rf verification/__pycache__
