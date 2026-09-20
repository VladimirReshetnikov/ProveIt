PYTHON ?= python3
PDFLATEX ?= pdflatex
NAME = ordinal_product_coherence

.PHONY: all verify clean
all: $(NAME).pdf

$(NAME).pdf: $(NAME).tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error $(NAME).tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error $(NAME).tex

verify:
	$(PYTHON) verify.py --output verification_results.json

clean:
	rm -f $(NAME).aux $(NAME).log $(NAME).out $(NAME).toc $(NAME).fls $(NAME).fdb_latexmk
