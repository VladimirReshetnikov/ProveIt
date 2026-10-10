PYTHON ?= python3

.PHONY: check optional numerical article all
check:
	$(PYTHON) code/run_checks.py
	$(PYTHON) code/check_resolution.py
	$(PYTHON) code/check_short_identities.py

optional:
	$(PYTHON) code/check_smith.py
	$(PYTHON) code/check_products_and_controls.py

numerical:
	$(PYTHON) code/numerical_checks.py

article:
	$(PYTHON) code/build_article.py

all: check optional numerical article
