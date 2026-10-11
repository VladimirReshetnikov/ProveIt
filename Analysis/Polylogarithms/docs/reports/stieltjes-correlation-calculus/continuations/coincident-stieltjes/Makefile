.PHONY: exact numeric pdf all
exact:
	python code/exact_engine.py
numeric:
	python code/verify_numerically.py
pdf:
	python code/build.py
all: exact numeric pdf
