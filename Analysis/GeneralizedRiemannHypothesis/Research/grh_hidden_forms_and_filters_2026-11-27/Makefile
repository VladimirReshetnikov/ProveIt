PDFLATEX ?= pdflatex
PYTHON ?= python3

.PHONY: pdf check figure clean

pdf:
	cd papers && $(PDFLATEX) -interaction=nonstopmode -halt-on-error hidden_symplectic_forms.tex
	cd papers && $(PDFLATEX) -interaction=nonstopmode -halt-on-error hidden_symplectic_forms.tex
	cd papers && $(PDFLATEX) -interaction=nonstopmode -halt-on-error hidden_symplectic_forms.tex
	cd papers && $(PDFLATEX) -interaction=nonstopmode -halt-on-error spectral_skewness.tex
	cd papers && $(PDFLATEX) -interaction=nonstopmode -halt-on-error spectral_skewness.tex

check:
	$(PYTHON) code/run_verification.py

figure:
	$(PYTHON) code/make_hidden_figure.py

clean:
	rm -f papers/*.aux papers/*.log papers/*.out papers/*.toc
