.PHONY: pdf examples lean verify

pdf:
	python3 build_pdf.py

examples:
	python3 verify.py

lean:
	cd lean && bash replay.sh

verify: examples lean pdf
