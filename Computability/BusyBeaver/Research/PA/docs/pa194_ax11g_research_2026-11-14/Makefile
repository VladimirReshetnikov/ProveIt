.PHONY: verify report

verify:
	python3 -B verify_all.py

report:
	python3 -B report/generate.py
	cd report && pdflatex -interaction=nonstopmode -halt-on-error main.tex
	cd report && pdflatex -interaction=nonstopmode -halt-on-error main.tex
