.PHONY: report verify verify-full
report:
	cd report && pdflatex -interaction=nonstopmode -halt-on-error report.tex
	cd report && pdflatex -interaction=nonstopmode -halt-on-error report.tex

verify:
	python3 -B verify.py

verify-full:
	python3 -B verify.py --full --novelty
