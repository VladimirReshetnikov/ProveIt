.PHONY: all verify examples clean

all: report.pdf

report.pdf: report.tex sections/guarded_core.tex sections/implementation.tex evidence/metrics_table.tex evidence/extra_metrics_table.tex evidence/validation_summary.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

verify:
	python3 scripts/reproduce.py

examples:
	python3 tests/build_root_cases.py
	python3 tests/audit_guarded_proofs.py

clean:
	latexmk -c report.tex
