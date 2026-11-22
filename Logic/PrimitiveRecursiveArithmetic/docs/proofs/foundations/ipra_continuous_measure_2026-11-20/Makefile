.PHONY: examples lean pdf verify
examples:
	python3 verify.py
lean:
	bash lean/replay.sh
pdf:
	python3 build_pdf.py
verify: examples lean pdf
