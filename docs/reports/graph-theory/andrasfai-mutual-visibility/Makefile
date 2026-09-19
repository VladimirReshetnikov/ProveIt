.PHONY: pdf check exhaustive symbolic data figure clean
PYTHON ?= python3
CXX ?= g++

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

check:
	$(PYTHON) code/verify.py

exhaustive:
	$(CXX) -O3 -std=c++17 code/exhaustive.cpp -o exhaustive
	./exhaustive 8 > data/exhaustive.json
	$(PYTHON) code/verify.py

symbolic:
	$(PYTHON) code/symbolic_certificate.py

data:
	$(PYTHON) code/visibility.py --write-data data

figure:
	$(PYTHON) code/make_figure.py

clean:
	rm -f article.aux article.log article.out article.toc exhaustive exhaustive.exe
	rm -rf code/__pycache__
