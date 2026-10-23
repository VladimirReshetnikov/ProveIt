.PHONY: verify pdf archive

verify:
	python3 verify_all.py

pdf:
	cd report && pdflatex -interaction=nonstopmode -halt-on-error report.tex
	cd report && pdflatex -interaction=nonstopmode -halt-on-error report.tex

archive:
	python3 package.py
