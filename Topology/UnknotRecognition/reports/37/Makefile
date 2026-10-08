PYTHON ?= python
.PHONY: test audit tables pdf verify certificates

test:
	PYTHONPATH=code $(PYTHON) -m unittest discover -s tests -v

audit:
	PYTHONPATH=code $(PYTHON) code/run_experiments.py

tables:
	$(PYTHON) code/make_tables.py

pdf:
	./build.sh

verify:
	$(PYTHON) code/check_manifest.py

certificates:
	@for f in examples/*.json; do PYTHONPATH=code $(PYTHON) -m separator_transfer verify "$$f" || exit 1; done
