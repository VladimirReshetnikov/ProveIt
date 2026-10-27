.PHONY: check pdf exhibits
check:
	python3 code/run_all.py
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
exhibits:
	python3 code/make_exhibits.py
