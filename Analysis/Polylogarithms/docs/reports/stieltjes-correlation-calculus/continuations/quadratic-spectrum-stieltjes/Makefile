.PHONY: pdf verify clean
pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

verify:
	python code/verify_exact.py --output build/exact_replay.json
	python code/verify_numeric.py --dps 45 --output build/numeric_replay.json

clean:
	latexmk -c article.tex
