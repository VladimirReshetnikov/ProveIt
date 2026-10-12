.PHONY: all verify tables integrity clean

all: article.pdf

article.pdf: article.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

verify:
	python verification/verify.py
	python verification/verify_supplemental.py

tables:
	python verification/export_tables.py

integrity:
	python verification/check_manifest.py

clean:
	latexmk -c article.tex
