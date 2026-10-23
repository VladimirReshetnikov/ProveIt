PYTHON ?= python3
PACKAGE_ROOT := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))

.PHONY: all verify pdf clean

all: verify pdf

verify:
	$(PYTHON) "$(PACKAGE_ROOT)reproduce.py"

pdf:
	latexmk -cd -pdf -interaction=nonstopmode -halt-on-error "$(PACKAGE_ROOT)report.tex"

clean:
	latexmk -cd -c "$(PACKAGE_ROOT)report.tex"
