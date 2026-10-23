.PHONY: verify verify-optimized pdf

verify:
	python3 verify_release.py

verify-optimized:
	python3 -O verify_release.py

pdf:
	cd report && pdflatex -interaction=nonstopmode -halt-on-error report.tex
	cd report && pdflatex -interaction=nonstopmode -halt-on-error report.tex
