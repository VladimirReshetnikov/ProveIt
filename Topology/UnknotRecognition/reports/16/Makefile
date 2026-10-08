PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: paper tables figure verify test patch

paper:
	cd article && $(PDFLATEX) -interaction=nonstopmode -halt-on-error unknot_dense_algebra.tex
	cd article && $(PDFLATEX) -interaction=nonstopmode -halt-on-error unknot_dense_algebra.tex
	cd article && $(PDFLATEX) -interaction=nonstopmode -halt-on-error unknot_dense_algebra.tex

tables:
	$(PYTHON) -B tools/build_tables.py --tables-only

figure:
	$(PYTHON) -B tools/build_tables.py

verify:
	$(PYTHON) -B tools/verify_bundle.py

test:
	cd implementation/fast && $(PYTHON) -B -m unittest discover -s tests -v

patch:
	$(PYTHON) -B tools/build_patch.py
