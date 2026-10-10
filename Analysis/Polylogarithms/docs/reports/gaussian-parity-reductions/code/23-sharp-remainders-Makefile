.PHONY: all pdf exact numeric figures checks clean

all: pdf

pdf: article.pdf

article.pdf: article.tex references.tex $(wildcard sections/*.tex) $(wildcard figures/*.pdf)
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

exact:
	python3 scripts/certify_s6.py --output data/s6_rational_certificate.json
	python3 scripts/verify_relation_spaces.py --output data/relation_space_certificates.json

numeric:
	python3 scripts/verify_moments.py --dps 180 --output data/moment_checks.json
	python3 scripts/verify_herglotz.py --dps 70 --output data/herglotz_checks.json
	python3 scripts/verify_tornheim.py --dps 80 --degree 120 --diagonal 240 --output data/tornheim_checks.json
	python3 scripts/verify_analytic_identities.py --output data/analytic_identity_checks.json
	python3 scripts/verify_s6_mellin.py --output data/s6_mellin_check.json
	python3 scripts/series_crosscheck.py --output data/series_crosscheck.json

figures:
	python3 scripts/make_figures.py

checks: exact numeric

clean:
	latexmk -c article.tex

