.PHONY: pdf verify figure clean

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error inverse_harmonic_transseries.tex
	pdflatex -interaction=nonstopmode -halt-on-error inverse_harmonic_transseries.tex

verify:
	python verification/verify.py
	python verification/certify.py

figure:
	python verification/make_figure.py

clean:
	rm -f inverse_harmonic_transseries.aux inverse_harmonic_transseries.log \
	      inverse_harmonic_transseries.out inverse_harmonic_transseries.toc
