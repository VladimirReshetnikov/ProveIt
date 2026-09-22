REPORT_DIR := $(abspath $(dir $(lastword $(MAKEFILE_LIST)))/..)

.PHONY: all test clean

all: $(REPORT_DIR)/article.pdf

$(REPORT_DIR)/article.pdf: $(REPORT_DIR)/article.tex
	cd "$(REPORT_DIR)" && latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

test:
	cd "$(REPORT_DIR)" && python3 code/run_all.py

clean:
	cd "$(REPORT_DIR)" && latexmk -c article.tex
