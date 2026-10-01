.PHONY: pdf verify clean

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error q_fabius_borel.tex
	pdflatex -interaction=nonstopmode -halt-on-error q_fabius_borel.tex
	pdflatex -interaction=nonstopmode -halt-on-error q_fabius_borel.tex

verify:
	python verify_results.py

clean:
	rm -f q_fabius_borel.aux q_fabius_borel.log q_fabius_borel.out q_fabius_borel.toc
