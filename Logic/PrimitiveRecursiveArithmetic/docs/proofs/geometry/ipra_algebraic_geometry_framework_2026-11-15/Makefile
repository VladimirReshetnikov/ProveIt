.PHONY: all test pdf manifest clean

all:
	bash build.sh

test:
	python3 -m unittest discover -s code -v

pdf:
	cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error ipra_algebraic_geometry_framework.tex

manifest:
	find . -type f ! -name MANIFEST.sha256 -print0 | sort -z | xargs -0 sha256sum > MANIFEST.sha256

clean:
	cd paper && latexmk -C ipra_algebraic_geometry_framework.tex
	rm -rf code/__pycache__
