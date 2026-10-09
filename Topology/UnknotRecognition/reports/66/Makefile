.PHONY: test audit benchmark patches ranks example pdf
PYTHON ?= python3
test:
	$(PYTHON) reproduce.py test
audit:
	$(PYTHON) reproduce.py audit --out results/new-audit.json
benchmark:
	$(PYTHON) reproduce.py benchmark --out results/new-benchmark.json
patches:
	$(PYTHON) reproduce.py patches --out results/new-patches.json
ranks:
	$(PYTHON) reproduce.py ranks
example:
	$(PYTHON) reproduce.py example
pdf:
	$(PYTHON) reproduce.py pdf
