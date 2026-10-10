.PHONY: exact diagnostics pdf check inventory all
PYTHON ?= python
exact:
	$(PYTHON) code/certify_euler.py
	$(PYTHON) code/verify_cyclotomic.py
diagnostics:
	$(PYTHON) code/verify_symbolic.py
	$(PYTHON) code/diagnostics.py
pdf:
	$(PYTHON) code/build.py
check:
	$(PYTHON) code/check_package.py
inventory:
	$(PYTHON) code/check_package.py --manifest
all: exact diagnostics pdf check
