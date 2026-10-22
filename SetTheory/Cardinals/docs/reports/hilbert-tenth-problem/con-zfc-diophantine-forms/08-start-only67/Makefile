.PHONY: check pdf
check:
	python3 checks/reproduce.py
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error diophantine_zfc.tex
	pdflatex -interaction=nonstopmode -halt-on-error diophantine_zfc.tex
	pdflatex -interaction=nonstopmode -halt-on-error direct_stack_core.tex
	pdflatex -interaction=nonstopmode -halt-on-error direct_stack_core.tex
