.PHONY: report verify

report:
	cd report && pdflatex -interaction=nonstopmode -halt-on-error report.tex
	cd report && pdflatex -interaction=nonstopmode -halt-on-error report.tex

verify:
	python3 comparison/verify_frontier.py
	python3 comparison/control_quotient.py
	python3 runtime193/check_runtime88301.py
	python3 runtime193/replay_fold88301.py
