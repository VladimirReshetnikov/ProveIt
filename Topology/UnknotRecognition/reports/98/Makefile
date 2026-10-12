PYTHON ?= python
export PYTHONPATH := src
.PHONY: test replay audit benchmark pdf clean

test:
	$(PYTHON) -m unittest discover -s tests -v

replay:
	$(PYTHON) experiments/replay_delivery.py

audit:
	$(PYTHON) experiments/audit.py

benchmark:
	$(PYTHON) experiments/benchmark.py

pdf:
	sh article/build.sh

clean:
	find . -type d -name __pycache__ -prune -exec rm -rf {} +
	rm -f article/*.aux article/*.log article/*.out article/*.toc
