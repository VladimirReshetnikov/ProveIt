PYTHON ?= python3
LATEXMK ?= latexmk

.PHONY: all integrity verify certificates figures pdf benchmarks clean

all: pdf

# Verify original delivered files before regenerating or modifying them.
integrity:
	$(PYTHON) -B code/verify_manifest.py

# Exact checks only; original recorded results remain unchanged.
verify:
	$(PYTHON) -B code/run_checks.py --output results/recheck

# Floating-point evaluations of the explicitly stated comparison model.
certificates:
	$(PYTHON) -B code/check_certificates.py --output results/new_certificates.json

# Regenerate exhibits from recorded data; requires matplotlib.
figures:
	$(PYTHON) -B code/build_exhibits.py

# Included figures and tables permit compilation without Python plotting.
pdf:
	mkdir -p build
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error -outdir=build report.tex
	cp build/report.pdf report.pdf

# Optional timing reruns; keep the originally delivered measurements.
benchmarks:
	$(PYTHON) -B code/verify_and_benchmark.py --repeats 3 --output results/new_benchmarks
	$(PYTHON) -B code/benchmark_projective.py --repetitions 3 --output results/new_projective

# Preserve report.pdf, figures, source files, and all recorded results.
clean:
	rm -rf build code/__pycache__
