.PHONY: all test figures pdf clean
all:
	bash build.sh

test:
	cd code && python3 -m unittest -v test_conway_core.py

figures:
	python3 figures/make_figures.py

pdf:
	cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error conway_criterion_ipra.tex

clean:
	cd paper && latexmk -C conway_criterion_ipra.tex
	rm -rf code/__pycache__
