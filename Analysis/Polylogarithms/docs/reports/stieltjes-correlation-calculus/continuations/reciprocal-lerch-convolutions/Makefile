.PHONY: all pdf verify exact standalone clean
all: verify pdf standalone
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
verify:
	python code/verify.py
exact:
	python code/verify.py --exact-only
standalone:
	python code/make_standalone.py
clean:
	rm -f *.aux *.log *.out *.toc *.fls *.fdb_latexmk
