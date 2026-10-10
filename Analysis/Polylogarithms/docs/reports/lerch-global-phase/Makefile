.PHONY: verify test pdf diagnostics clean
verify:
	python3 code/verify_exact.py

test:
	python3 code/test_exact.py

pdf:
	cd article && pdflatex -interaction=nonstopmode -halt-on-error lerch_global_phase.tex
	cd article && pdflatex -interaction=nonstopmode -halt-on-error lerch_global_phase.tex
	cd article && pdflatex -interaction=nonstopmode -halt-on-error lerch_global_phase.tex

diagnostics:
	python3 code/numerical_diagnostics.py --dps 40

clean:
	rm -f article/*.aux article/*.log article/*.out article/*.toc
