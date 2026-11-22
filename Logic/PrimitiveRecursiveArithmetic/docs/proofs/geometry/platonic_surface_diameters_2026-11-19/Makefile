.PHONY: pdf check lean figures
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error platonic_surface.tex
	pdflatex -interaction=nonstopmode -halt-on-error platonic_surface.tex

check:
	python3 scripts/icosahedron.py
	python3 scripts/dodeca_model.py
	python3 scripts/dodeca_lower.py
	python3 scripts/dodeca_upper.py
	python3 scripts/dodeca_calibration.py

lean:
	./lean/check.sh "$(PROVEIT)"

figures:
	python3 scripts/draw_small.py
	python3 scripts/draw_ico_strips.py figures/ico_strips.pdf
	python3 scripts/dodeca_figure.py
