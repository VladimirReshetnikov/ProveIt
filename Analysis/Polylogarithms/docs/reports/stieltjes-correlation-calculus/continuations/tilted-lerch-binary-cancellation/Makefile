.PHONY: all verify inspect
all:
	python code/build.py
verify:
	python code/verify_exact.py
	python code/verify_numerical.py --dps 45
	python code/verify_numerical.py --dps 60
inspect:
	python code/inspect_pdf.py
