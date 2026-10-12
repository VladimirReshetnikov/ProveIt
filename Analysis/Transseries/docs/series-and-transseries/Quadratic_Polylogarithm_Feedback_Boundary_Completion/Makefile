PYTHON ?= python3
LATEXMK ?= latexmk

.PHONY: all pdf figures verify clean

all: pdf

pdf: figures
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error article.tex

figures:
	$(PYTHON) code/make_figures.py

verify:
	$(PYTHON) code/feedback_verify.py --output-dir data
	$(PYTHON) code/verify_coefficient_crossover.py --output-dir data
	$(PYTHON) code/verify_critical_charts.py --output-dir data
	$(PYTHON) code/verify_crossover.py --output-dir data
	$(PYTHON) code/verify_joint_crossover.py --output-dir data --X 40 80 --dps 180

clean:
	$(LATEXMK) -c article.tex
