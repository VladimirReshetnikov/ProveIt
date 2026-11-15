PYTHON ?= python3
LATEXMK ?= latexmk

.PHONY: all pdf check hashes clean

all: check pdf hashes

check:
	$(PYTHON) code/pappus_checker.py certificates/sample_certificate.json | tee verification_output.txt

pdf:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error pappus_centroid_ipra.tex

hashes:
	find . -type f \
	  ! -path './build/*' ! -path '*/__pycache__/*' ! -name '*.pyc' \
	  ! -name 'SHA256SUMS' \
	  ! -name '*.aux' ! -name '*.fdb_latexmk' ! -name '*.fls' \
	  ! -name '*.log' ! -name '*.out' ! -name '*.toc' \
	  -print0 | sort -z | xargs -0 sha256sum > SHA256SUMS

clean:
	$(LATEXMK) -C pappus_centroid_ipra.tex
	rm -f SHA256SUMS
