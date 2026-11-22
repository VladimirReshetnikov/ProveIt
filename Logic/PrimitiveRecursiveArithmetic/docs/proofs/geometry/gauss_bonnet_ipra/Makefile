.PHONY: report checks

report:
	cd paper && mkdir -p build && latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build gauss_bonnet_ipra.tex
	cp paper/build/gauss_bonnet_ipra.pdf gauss_bonnet_ipra.pdf

checks:
	python3 tools/finite_certificate.py > tools/finite_certificate_results.json
	python3 tools/discrete_green.py > validation/discrete_green_results.json
	python3 tools/smooth_examples.py --output examples/smooth_results.json
