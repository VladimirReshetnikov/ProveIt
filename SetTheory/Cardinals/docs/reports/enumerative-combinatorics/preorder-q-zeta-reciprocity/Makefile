.PHONY: all pdf check smoke clean

all: pdf check

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

check:
	python3 -m unittest discover -s code
	python3 code/verify.py --exhaustive 5 --random-per-size 16 \
	    --seed 20260920 --output data/verification.json
	python3 code/verify_transfer.py --output data/verification_transfer.json
	python3 code/verify_supportwise.py \
	    --output data/verification_supportwise.json

smoke:
	python3 code/verify.py --exhaustive 3 --random-per-size 4 \
	    --output data/smoke.json

clean:
	latexmk -c
	rm -f article.fls article.fdb_latexmk
