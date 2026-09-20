PYTHON ?= python
export PYTHONPATH := code

.NOTPARALLEL:

.PHONY: all verify verify-signed cross certificates tables pdf clean

all: verify verify-signed cross certificates tables pdf

verify:
	$(PYTHON) code/verify.py --symbolic > data/verification_transcript.txt

verify-signed:
	$(PYTHON) code/verify_signed.py > data/verification_signed_console.txt
	$(PYTHON) code/test_api.py > data/api_tests.txt 2>&1

cross:
	$(PYTHON) code/cross_check.py > data/cross_check.txt

certificates:
	$(PYTHON) code/check_certificates.py > data/certificate_verification.txt

tables:
	$(PYTHON) code/growth_constants.py
	$(PYTHON) code/make_tex_tables.py

pdf:
	latexmk -pdf -interaction=nonstopmode article.tex
	latexmk -c

clean:
	latexmk -c
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk
	rm -rf code/__pycache__
