.PHONY: all standalone clean

all: standalone
	latexmk -pdf -interaction=nonstopmode -halt-on-error Barnes_Resolvents_and_Harmonic_Identities.tex

standalone:
	python3 build_standalone.py

clean:
	latexmk -c Barnes_Resolvents_and_Harmonic_Identities.tex
