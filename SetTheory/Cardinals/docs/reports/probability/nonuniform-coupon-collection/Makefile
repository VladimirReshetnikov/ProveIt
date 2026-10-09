.PHONY: paper test experiments all

paper:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -cd article/coupon_collector.tex

test:
	python -m unittest discover -s tests -v

experiments:
	python experiments/run_experiments.py
	python experiments/sharp_scalar.py

all: test paper
