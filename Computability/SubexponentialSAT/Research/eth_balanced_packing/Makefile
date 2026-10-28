.PHONY: pdf checks verify

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

checks:
	python3 checks/check_packing.py
	python3 checks/check_analysis.py

verify:
	python3 checks/verify_manifest.py
