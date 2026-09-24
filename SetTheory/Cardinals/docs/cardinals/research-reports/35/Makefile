LATEX = pdflatex
PYTHON = python3
NAME = Prikry_Choice_and_Maximal_Rigidity

.PHONY: all check clean
all: $(NAME).pdf

$(NAME).pdf: $(NAME).tex
	$(LATEX) -interaction=nonstopmode -halt-on-error $(NAME).tex
	$(LATEX) -interaction=nonstopmode -halt-on-error $(NAME).tex

check:
	$(PYTHON) finite_checks.py

clean:
	rm -f $(NAME).aux $(NAME).log $(NAME).out $(NAME).toc
