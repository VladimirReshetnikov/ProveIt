.PHONY: all inventory check pdf clean

all: check pdf

inventory:
	python3 code/build_inventory.py

check: inventory
	python3 code/elementary_checks.py
	python3 code/quadratic_checks.py
	python3 code/verify_diophantine.py
	python3 code/analytic_checks.py
	python3 code/algebraic_checks.py
	python3 code/transcendence_checks.py

pdf: inventory
	latexmk -pdf -interaction=nonstopmode -halt-on-error number_theory_ipra.tex

clean:
	latexmk -c number_theory_ipra.tex
