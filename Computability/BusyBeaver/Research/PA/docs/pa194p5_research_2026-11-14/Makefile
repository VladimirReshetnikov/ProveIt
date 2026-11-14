.PHONY: verify report

verify:
	python3 verify.py
	python3 comparison/verify_novelty.py
	python3 comparison/verify_census.py

report:
	cd report && pdflatex -interaction=nonstopmode -halt-on-error report.tex
	cd report && pdflatex -interaction=nonstopmode -halt-on-error report.tex

