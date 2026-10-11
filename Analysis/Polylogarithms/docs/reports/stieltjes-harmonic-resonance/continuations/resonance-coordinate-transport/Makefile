.PHONY: all pdf standalone checks

all: pdf

pdf:
	python3 build.py

standalone:
	python3 build.py --assemble-only

checks:
	python3 code/verify_all.py
