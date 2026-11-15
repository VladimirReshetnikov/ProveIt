.PHONY: all pdf check lean clean

all: pdf check

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error diophantine_geometry_ipra.tex

check:
	python3 code/check_all.py

lean:
	cd lean && lake build

clean:
	latexmk -c diophantine_geometry_ipra.tex
