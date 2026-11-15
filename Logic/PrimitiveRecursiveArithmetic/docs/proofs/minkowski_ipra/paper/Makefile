.PHONY: all clean
all: minkowski_ipra.pdf

minkowski_ipra.pdf: $(wildcard *.tex) finite_minkowski.pdf
	pdflatex -interaction=nonstopmode -halt-on-error minkowski_ipra.tex
	pdflatex -interaction=nonstopmode -halt-on-error minkowski_ipra.tex
	pdflatex -interaction=nonstopmode -halt-on-error minkowski_ipra.tex

clean:
	rm -f minkowski_ipra.aux minkowski_ipra.log minkowski_ipra.out minkowski_ipra.toc
