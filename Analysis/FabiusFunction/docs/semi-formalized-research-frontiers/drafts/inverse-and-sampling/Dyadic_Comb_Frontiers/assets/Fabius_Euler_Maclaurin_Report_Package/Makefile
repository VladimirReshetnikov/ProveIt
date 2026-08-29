PYTHON ?= python3
LATEXMK ?= latexmk
REPORT := fabius_euler_maclaurin_report

.PHONY: all experiments pdf clean

all: experiments pdf

experiments:
	$(PYTHON) fabius_em_experiments.py --output-dir data --max-power 10 --max-level 10

pdf:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error $(REPORT).tex

clean:
	$(LATEXMK) -C $(REPORT).tex
	rm -f data/plot_warning.txt
