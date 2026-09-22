.PHONY: all test clean

PACKAGE_ROOT := $(abspath $(dir $(lastword $(MAKEFILE_LIST)))/..)
PYTHON ?= python3
LATEXMK ?= latexmk

all: $(PACKAGE_ROOT)/article.pdf

$(PACKAGE_ROOT)/article.pdf: $(PACKAGE_ROOT)/article.tex
	cd "$(PACKAGE_ROOT)" && $(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error article.tex

test:
	$(PYTHON) "$(PACKAGE_ROOT)/code/run_all.py"

clean:
	cd "$(PACKAGE_ROOT)" && $(LATEXMK) -c article.tex
