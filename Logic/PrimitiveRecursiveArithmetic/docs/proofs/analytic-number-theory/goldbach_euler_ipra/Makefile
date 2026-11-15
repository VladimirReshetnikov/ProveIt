.PHONY: all paper checks clean

all: paper checks

paper:
	latexmk -pdf -interaction=nonstopmode -halt-on-error goldbach_euler_ipra.tex

checks:
	python checks/finite_check.py --output-dir checks --canonical-limit 3000

clean:
	latexmk -c goldbach_euler_ipra.tex
