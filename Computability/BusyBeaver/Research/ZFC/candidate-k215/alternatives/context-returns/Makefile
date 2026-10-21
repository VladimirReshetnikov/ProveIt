PYTHON ?= python3
export PYTHONOPTIMIZE :=

.PHONY: check source-regressions runtime pdf

check:
	$(PYTHON) code/verify_context.py
	$(PYTHON) code/audit_shallow.py
	$(PYTHON) code/audit_runtime_receipts.py
	$(PYTHON) research/verify_cache_transfer.py

source-regressions:
	$(PYTHON) research/build_cache_transfer.py

runtime:
	$(PYTHON) code/runtime-inputs/validate_native.py machine/k215-context.native.tm machine/sites215.json reproduction/context-runtime
	$(PYTHON) code/runtime-inputs/validate_native.py machine/k215-shallow.native.tm machine/sites-shallow.json reproduction/shallow-runtime

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

