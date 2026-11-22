.PHONY: examples lean pdf figure verify

examples:
	python3 verify.py

lean:
	cd lean && lake build

pdf:
	python3 build_pdf.py

figure:
	python3 code/plot_observations.py

verify: examples lean pdf
