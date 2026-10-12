PYTHON ?= python3
export PYTHONPATH := code

.PHONY: test verify audit benchmark article clean

test:
	$(PYTHON) -m unittest discover -s tests -v

verify:
	$(PYTHON) verify_artifacts.py

audit:
	$(PYTHON) experiments/audit.py

benchmark:
	$(PYTHON) experiments/benchmark.py

article:
	cd article && sh build.sh

clean:
	find . -type d -name __pycache__ -prune -exec rm -rf {} +
	rm -f article/*.aux article/*.log article/*.out article/*.toc
