.PHONY: all pdf verify diagnostics figures clean package

all: pdf

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error article.tex

verify:
	python code/verify_all.py

diagnostics:
	python code/verify_all.py --diagnostics

figures:
	python code/kernel_diagnostics.py
	python code/plot_order_profile.py
	python code/plot_mesh_threshold.py

clean:
	latexmk -c article.tex

package:
	python code/package_release.py
