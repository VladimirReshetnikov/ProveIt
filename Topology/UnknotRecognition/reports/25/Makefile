.PHONY: test paper bench package

test:
	python -m unittest discover -s tests -v

paper:
	cd docs && sh build.sh

bench:
	python scripts/benchmark.py --rounds 7
	python scripts/radius_experiment.py

package: paper
	python scripts/package.py
