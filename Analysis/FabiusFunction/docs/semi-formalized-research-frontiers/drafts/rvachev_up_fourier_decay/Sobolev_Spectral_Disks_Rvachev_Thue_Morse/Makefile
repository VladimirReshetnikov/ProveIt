.PHONY: pdf verify clean

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

# ed. (2026-09-29): writes rerun/, not the recorded verification.json/.log.
verify:
	mkdir -p rerun
	python3 verify.py --output rerun/verification.json > rerun/verification.log
	cat rerun/verification.log

clean:
	rm -f article.aux article.log article.out article.toc
