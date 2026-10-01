.PHONY: pdf verify exact clean
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
verify:
	python3 reproducibility/verify.py
exact:
	python3 reproducibility/verify.py --exact-only --output validation/exact_results.json
clean:
	rm -f article.aux article.log article.out article.toc
