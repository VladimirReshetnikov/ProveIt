.PHONY: verify verify-optimized pdf

verify:
	python3 -B verify.py

verify-optimized:
	python3 -B -O verify.py

pdf:
	cd report && pdflatex -interaction=nonstopmode -halt-on-error report.tex
	cd report && pdflatex -interaction=nonstopmode -halt-on-error report.tex
