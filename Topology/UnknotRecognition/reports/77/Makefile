PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: check reproduce pdf clean

check:
	$(PYTHON) -m unittest discover -s tests -v

reproduce:
	$(PYTHON) reproduce.py --output-dir results-rerun

pdf:
	cd paper && $(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	cd paper && $(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	cd paper && $(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex

clean:
	$(PYTHON) -c "from pathlib import Path; [p.unlink() for p in Path('paper').iterdir() if p.suffix in ('.aux','.log','.out','.toc')]"
