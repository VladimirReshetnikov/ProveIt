.PHONY: all pdf test benchmark clean
all: test pdf
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
test:
	python tools/run_tests.py
benchmark:
	python tools/benchmark.py
clean:
	rm -f article.aux article.log article.out article.toc
