.PHONY: all paper test benchmark clean
all: paper

paper:
	cd article && pdflatex -interaction=nonstopmode -halt-on-error fourier_total_variation.tex
	cd article && pdflatex -interaction=nonstopmode -halt-on-error fourier_total_variation.tex

test:
	python tests/run_checks.py

benchmark:
	python tests/benchmark.py

clean:
	rm -f article/*.aux article/*.log article/*.out article/*.toc article/*.blg
	rm -rf code/__pycache__ tests/__pycache__
