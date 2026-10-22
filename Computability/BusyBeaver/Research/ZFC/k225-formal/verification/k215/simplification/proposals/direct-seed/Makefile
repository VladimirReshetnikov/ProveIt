PYTHON ?= python3
LEAN ?= $(shell command -v lean)
COQC ?= coqc
COQCHK ?= coqchk
ROOT := $(abspath $(dir $(lastword $(MAKEFILE_LIST))))
PRODUCER := $(ROOT)/producer/repository/Computability/BusyBeaver/Research/ZFC/k225-formal/generate_dominated_implication_lean.py

.PHONY: pdf check-inputs check-producer lean rocq

pdf:
	mkdir -p build/pdf
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build/pdf report.tex
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build/pdf report.tex
	cp build/pdf/report.pdf report.pdf

check-inputs:
	$(PYTHON) lean/reproduce.py --lean unused --out unused --check-only
	$(PYTHON) rocq/reproduce.py --verify-only

check-producer:
	$(PYTHON) "$(PRODUCER)" --check

lean:
	$(PYTHON) lean/reproduce.py --lean "$(LEAN)" --out "$(ROOT)/build/lean"

rocq:
	$(PYTHON) rocq/reproduce.py --coqc "$(COQC)" --coqchk "$(COQCHK)" --out "$(ROOT)/build/rocq"
