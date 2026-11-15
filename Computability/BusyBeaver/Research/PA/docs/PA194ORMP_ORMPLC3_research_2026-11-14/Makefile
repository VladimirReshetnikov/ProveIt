.PHONY: verify quick report
verify:
	python3 -B verify.py
quick:
	python3 -B verify.py --quick
report:
	python3 -B report/generate_tables.py
	cd report && pdflatex -interaction=nonstopmode -halt-on-error report.tex
	cd report && pdflatex -interaction=nonstopmode -halt-on-error report.tex
