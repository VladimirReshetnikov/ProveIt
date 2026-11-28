.PHONY: pdf check clean
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error torsion_power_patterns.tex
	pdflatex -interaction=nonstopmode -halt-on-error torsion_power_patterns.tex
	pdflatex -interaction=nonstopmode -halt-on-error torsion_power_patterns.tex
check:
	python3 check_patterns.py > checks.txt
	python3 check_small_grid.py > grid_checks.txt
clean:
	rm -f torsion_power_patterns.aux torsion_power_patterns.log torsion_power_patterns.out torsion_power_patterns.toc
