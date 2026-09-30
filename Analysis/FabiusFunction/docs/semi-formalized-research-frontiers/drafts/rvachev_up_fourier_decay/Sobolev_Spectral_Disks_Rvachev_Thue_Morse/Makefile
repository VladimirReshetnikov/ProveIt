.PHONY: pdf verify clean

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

verify:
	python3 verify.py --output verification.json > verification.log
	cat verification.log

clean:
	rm -f article.aux article.log article.out article.toc
