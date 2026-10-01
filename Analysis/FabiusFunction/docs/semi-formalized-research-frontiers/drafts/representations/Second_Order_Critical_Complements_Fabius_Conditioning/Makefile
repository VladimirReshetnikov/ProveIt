NAME = Second_Order_Fabius_Crossover

.PHONY: all check clean
all:
	pdflatex -interaction=nonstopmode -halt-on-error $(NAME).tex
	pdflatex -interaction=nonstopmode -halt-on-error $(NAME).tex
	pdflatex -interaction=nonstopmode -halt-on-error $(NAME).tex

check:
	python check_gamma.py

clean:
	rm -f $(NAME).aux $(NAME).log $(NAME).out
