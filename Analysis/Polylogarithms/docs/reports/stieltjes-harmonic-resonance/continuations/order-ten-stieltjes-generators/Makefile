SHELL := /bin/bash
.SHELLFLAGS := -eu -o pipefail -c
PYTHON ?= python3
LATEXMK ?= latexmk
LATEXPAND ?= latexpand

.PHONY: all verify pdf singlefile checksums clean

all: verify pdf singlefile checksums

verify:
	$(PYTHON) verification/run_all.py | tee verification/VERIFICATION_LOG.txt

pdf:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error article.tex

singlefile:
	$(LATEXPAND) article.tex > article_singlefile.tex
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error -jobname=article_singlefile_check article_singlefile.tex
	rm -f article_singlefile_check.pdf article_singlefile_check.aux article_singlefile_check.fdb_latexmk article_singlefile_check.fls article_singlefile_check.log article_singlefile_check.out article_singlefile_check.toc

checksums:
	find . -type f \
	  ! -name 'CHECKSUMS.sha256' \
	  ! -path './build/*' \
	  ! -name '*.aux' ! -name '*.fdb_latexmk' ! -name '*.fls' ! -name '*.log' ! -name '*.out' ! -name '*.toc' \
	  ! -path '*/__pycache__/*' -print0 | sort -z | xargs -0 sha256sum > CHECKSUMS.sha256

clean:
	$(LATEXMK) -C article.tex || true
	rm -f article_singlefile_check.*
	find . -type d -name __pycache__ -prune -exec rm -rf {} +
