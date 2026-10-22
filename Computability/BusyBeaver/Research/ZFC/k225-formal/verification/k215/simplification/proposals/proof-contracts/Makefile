.PHONY: report check

report:
	mkdir -p build-report
	pdflatex -halt-on-error -interaction=nonstopmode -output-directory=build-report report.tex
	pdflatex -halt-on-error -interaction=nonstopmode -output-directory=build-report report.tex
	cp build-report/report.pdf report.pdf

check:
	python3 verify.py
	python3 audit_snapshot.py --check
