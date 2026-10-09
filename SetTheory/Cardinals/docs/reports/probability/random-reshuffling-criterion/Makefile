.PHONY: all pdf verify example clean
all: verify pdf
pdf:
	./build.sh
verify:
	python tests/verify.py
	python tests/explicit_example.py
example:
	python code/classify.py certificates/two_component_input.json --output certificates/two_component_certificate.json
clean:
	rm -rf build code/__pycache__ tests/__pycache__
