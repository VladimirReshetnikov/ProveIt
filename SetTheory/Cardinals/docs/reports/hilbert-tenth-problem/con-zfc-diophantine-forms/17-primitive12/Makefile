PYTHON ?= python3
LATEX ?= pdflatex

.PHONY: verify degrees pdf clean

# Check mathematical artifacts; do not infer a formal proof from these checks.
verify:
	$(PYTHON) verification/check_package.py --skip-manifest
	$(PYTHON) arithmetic/primitive12/verify_primitive12.py
	$(PYTHON) arithmetic/integer26/verify_integer26.py
	$(PYTHON) arithmetic/integer27/build_integer27.py
	$(PYTHON) compiler/check_pruned_t4.py
	$(PYTHON) compiler/coefficient_residues.py --modulus 1000000007 --verify --receipt compiler/coefficient_residue_verification.json

# Slower exact finite-field degree corroboration, using only the standard library.
degrees:
	$(PYTHON) arithmetic/primitive12/build_primitive12.py --degree-check
	$(PYTHON) arithmetic/integer26/build_integer26.py --out arithmetic/integer26/generated --degree-check

pdf:
	$(LATEX) -interaction=nonstopmode -halt-on-error report.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error report.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error report.tex

clean:
	rm -f report.aux report.log report.out report.toc
