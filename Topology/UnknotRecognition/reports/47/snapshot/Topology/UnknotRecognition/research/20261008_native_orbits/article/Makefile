MAIN := unknot_native_orbits

.PHONY: all regenerate clean

all:
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(MAIN).tex

# Requires the supplied relative repository layout and matplotlib.
# Already-generated tables and vector figures are included for TeX-only builds.
regenerate:
	python3 generate_measurements.py

clean:
	latexmk -c $(MAIN).tex
