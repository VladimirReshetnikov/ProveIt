PYTHON ?= python3
.PHONY: pdf verify standalone clean
pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build article.tex
	cp build/article.pdf article.pdf
verify:
	$(PYTHON) verification/run_all.py
standalone:
	$(PYTHON) tools/make_standalone.py
clean:
	rm -rf build
