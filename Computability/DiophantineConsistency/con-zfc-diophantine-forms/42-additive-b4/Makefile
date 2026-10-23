.PHONY: verify pdf archive clean

verify:
	python3 reproduce.py

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

archive: verify pdf
	python3 package_release.py

clean:
	latexmk -c report.tex
