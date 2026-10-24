.PHONY: verify verify-optimized pdf archive

verify:
	python3 verify_all.py

verify-optimized:
	python3 -O verify_all.py

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

archive:
	python3 make_archive.py
