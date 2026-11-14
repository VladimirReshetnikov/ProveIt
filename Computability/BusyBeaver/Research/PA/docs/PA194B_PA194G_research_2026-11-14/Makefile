PYTHON ?= python3
LATEX ?= pdflatex

.PHONY: all verify runtime independent-g tables pdf replay-startups
all: verify pdf

verify:
	$(PYTHON) -B verification/check_transfer.py
	$(PYTHON) -B generalizer/check_commands.py
	$(PYTHON) -B comparison/replay/verify_generalizer_novelty.py --candidate generalizer/machine.tm --output verification/generalizer_novelty.json

runtime:
	$(PYTHON) -B verify_build.py
	$(PYTHON) -B generalizer/build.py --output verification/generalizer_rebuild

independent-g:
	cd generalizer && $(PYTHON) -B independent/check.py . --output independent/replay

tables:
	$(PYTHON) -B report/generate_tables.py

pdf:
	cd report && $(LATEX) -interaction=nonstopmode -halt-on-error pa194_report.tex
	cd report && $(LATEX) -interaction=nonstopmode -halt-on-error pa194_report.tex

replay-startups:
	$(PYTHON) -B comparison/replay/audit_193_startups.py --steps 10000 --output verification/startup193_replay.json
