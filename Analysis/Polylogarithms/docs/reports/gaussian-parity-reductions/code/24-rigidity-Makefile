PYTHON ?= python3
TEX := polylogarithms_rigidity

.PHONY: pdf checks figure clean

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build $(TEX).tex
	$(PYTHON) -c "from pathlib import Path; import shutil; shutil.copyfile(Path('build') / '$(TEX).pdf', '$(TEX).pdf')"

checks:
	$(PYTHON) code/run_checks.py

figure:
	$(PYTHON) code/verify_saddle.py --figure

clean:
	latexmk -c -outdir=build $(TEX).tex
