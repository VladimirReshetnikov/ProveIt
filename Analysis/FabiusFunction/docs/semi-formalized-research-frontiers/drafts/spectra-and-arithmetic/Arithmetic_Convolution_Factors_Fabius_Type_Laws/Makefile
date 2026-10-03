.PHONY: all pdf verify clean

all: pdf verify

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

# ed. (2026-10-01): writes rerun/ instead of overwriting the recorded verification_results.json.
verify:
	python3 verify.py --output rerun/verification_results.json

clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk
