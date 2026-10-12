.PHONY: pdf verify clean
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
verify:
	python code/verify.py --output-dir replay
clean:
	rm -f article.aux article.log article.out article.toc
