.PHONY: verify literal tables pdf

verify:
	python3 -B verify.py

literal:
	python3 -B verify.py --literal

tables:
	python3 report/make_tables.py

pdf: tables
	cd report && pdflatex -interaction=nonstopmode -halt-on-error pa194gh_report.tex
	cd report && pdflatex -interaction=nonstopmode -halt-on-error pa194gh_report.tex
