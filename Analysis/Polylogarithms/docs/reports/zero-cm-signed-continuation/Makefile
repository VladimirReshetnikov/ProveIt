PYTHON ?= python3
LATEX ?= lualatex

.PHONY: pdf exact symbolic diagnostics figures standalone clean

pdf:
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex

exact:
	$(PYTHON) code/replay_exact.py

symbolic:
	$(PYTHON) code/compile_saddle_coefficients.py

diagnostics:
	$(PYTHON) code/check_uniform_saddle.py --dps 75
	$(PYTHON) code/check_gamma_joint_asymptotics.py
	$(PYTHON) code/check_lerch_endpoint.py
	$(PYTHON) code/scan_lerch_integral.py
	$(PYTHON) code/search_s8.py
	$(PYTHON) code/integral_audit.py

figures:
	$(PYTHON) code/plot_harmonic_saddle.py
	$(PYTHON) code/plot_gamma_joint.py

standalone:
	$(PYTHON) code/make_standalone.py

clean:
	rm -f article.aux article.log article.out article.toc
	rm -f polylogarithms_saddles_and_zeros.aux polylogarithms_saddles_and_zeros.log polylogarithms_saddles_and_zeros.out polylogarithms_saddles_and_zeros.toc

