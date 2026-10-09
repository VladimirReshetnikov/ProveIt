.PHONY: test audit replay patch-check benchmark tables pdf verify release

test:
	python -m unittest discover -s tests -v

audit:
	python tools/audit.py

replay:
	python tools/replay_examples.py

patch-check:
	python tools/check_patch.py

benchmark:
	python tools/benchmark.py --repeats 2 --output results/benchmark_rerun.json

tables:
	python tools/make_tables.py

pdf: tables
	cd paper && pdflatex -interaction=nonstopmode -halt-on-error article.tex
	cd paper && pdflatex -interaction=nonstopmode -halt-on-error article.tex
	cd paper && pdflatex -interaction=nonstopmode -halt-on-error article.tex

verify:
	python tools/check_manifest.py

release:
	python tools/make_release.py
