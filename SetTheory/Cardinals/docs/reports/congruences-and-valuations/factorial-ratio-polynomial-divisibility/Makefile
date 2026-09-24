.PHONY: pdf verify test regenerate clean
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
verify:
	python3 code/verify_certificates.py
test:
	python3 code/test_research.py
regenerate:
	python3 code/generate_artifacts.py
	python3 code/verify_certificates.py
clean:
	rm -f article.aux article.log article.out article.toc
