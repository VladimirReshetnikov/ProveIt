.PHONY: all pdf verify figure clean

all: pdf

pdf:
	xelatex -no-pdf -interaction=nonstopmode -halt-on-error uniform_geometric_avoidance.tex
	xelatex -no-pdf -interaction=nonstopmode -halt-on-error uniform_geometric_avoidance.tex
	xelatex -no-pdf -interaction=nonstopmode -halt-on-error uniform_geometric_avoidance.tex
	! grep -q 'There were undefined references' uniform_geometric_avoidance.log
	xdvipdfmx -o uniform_geometric_avoidance.pdf uniform_geometric_avoidance.xdv

verify:
	python3 verification/verify_exact.py

figure:
	python3 figures/make_figure.py

clean:
	rm -f uniform_geometric_avoidance.aux uniform_geometric_avoidance.log uniform_geometric_avoidance.out uniform_geometric_avoidance.toc uniform_geometric_avoidance.xdv

