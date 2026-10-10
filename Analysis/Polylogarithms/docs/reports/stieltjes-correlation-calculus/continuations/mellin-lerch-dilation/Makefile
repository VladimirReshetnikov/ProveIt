PYTHON ?= python3
ARTICLE = Mellin_Lerch_and_Stieltjes_Dilation

.PHONY: pdf check-exact check-numeric summary fragment clean

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(ARTICLE).tex

check-exact:
	$(PYTHON) code/exact_identity_engine.py

check-numeric:
	$(PYTHON) code/verify_mellin_rows.py
	$(PYTHON) code/verify_mellin_master.py
	$(PYTHON) code/derive_parity.py
	$(PYTHON) code/check_dilated_polygamma.py
	$(PYTHON) code/check_dilated_stieltjes.py
	$(PYTHON) code/check_jets_section.py
	$(PYTHON) code/check_pi_squared.py
	$(PYTHON) code/summarize_verification.py

summary:
	$(PYTHON) code/summarize_verification.py

fragment:
	$(PYTHON) code/build_integration_fragment.py

clean:
	latexmk -c $(ARTICLE).tex
