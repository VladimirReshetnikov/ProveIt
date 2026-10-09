.PHONY: test audit benchmark article check-example

test:
	python3 -m unittest discover -s tests -v

audit:
	python3 -m experiments.audit

benchmark:
	python3 -m experiments.benchmark
	python3 -m experiments.make_tables

article:
	sh build.sh

check-example:
	python3 -m rooted_disc examples/workload.json --check
