.PHONY: pdf verify pitfall clean
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

# Preserve the delivered evidence by writing replay outputs separately.
verify:
	python code/verify.py --output-dir replay --max-n 256

pitfall:
	python code/differentiation_pitfall.py

clean:
	rm -f article.aux article.log article.out article.toc
