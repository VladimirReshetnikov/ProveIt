PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: all check pdf integrity

all: check pdf

check:
	mkdir -p data verification
	$(PYTHON) code/check_ideal_density.py --output data/ideal_density_certificate.json > verification/ideal_density_check.log
	$(PYTHON) code/verify_ideal_natural_gain.py --output data/ideal_natural_gain_certificate.json > verification/ideal_natural_gain_verification.log
	$(PYTHON) code/check_source_twists.py > verification/source_twists_check.log
	$(PYTHON) code/check_module_bridge.py --output data/module_bridge_checks.json > verification/module_bridge_checks.log
	$(PYTHON) code/verify_ktheory_prefilter.py --ranks --output data/ktheory_prefilter_rerun.json > verification/ktheory_prefilter_rerun.log

pdf:
	mkdir -p verification
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error report.tex > verification/latex_first_pass.log
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error report.tex > verification/latex_final_pass.log

integrity:
	sha256sum -c SHA256SUMS
