.PHONY: pdf verify selection clean

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

verify:
	python3 -B code/verify.py --max-k 40

selection:
	python3 -B code/select_area.py

clean:
	rm -f article.aux article.log article.out article.toc
