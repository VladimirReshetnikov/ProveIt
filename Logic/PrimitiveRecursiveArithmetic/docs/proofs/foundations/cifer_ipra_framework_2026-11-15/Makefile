.PHONY: all test demo pdf clean

all: test demo pdf

test:
	cd code && python3 -m unittest -v test_cifer.py

demo:
	cd code && python3 demo.py

pdf:
	cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error cifer_ipra_framework.tex

clean:
	cd paper && latexmk -C
