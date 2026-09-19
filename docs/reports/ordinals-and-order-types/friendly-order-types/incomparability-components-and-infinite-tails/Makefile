.PHONY: all test verify clean
all:
	python build.py

test:
	python -m unittest discover -s code -v

verify:
	python code/verify.py --max-n 7 --grid-max 6 --output results/verification.json

clean:
	rm -f friendly_order_types.aux friendly_order_types.log friendly_order_types.out
	rm -f friendly_order_types.toc friendly_order_types.blg friendly_order_types.fls
	rm -f friendly_order_types.fdb_latexmk
