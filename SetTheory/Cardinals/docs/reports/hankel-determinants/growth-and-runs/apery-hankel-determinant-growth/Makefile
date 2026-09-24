.PHONY: pdf verify figures clean

pdf:
	mkdir -p build
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build apery_hankel_growth.tex
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build apery_hankel_growth.tex
	cp build/apery_hankel_growth.pdf apery_hankel_growth.pdf

verify:
	python3 code/verify.py

figures:
	python3 code/make_figures.py

build/apery_gmp: code/apery_gmp.cpp
	mkdir -p build
	g++ -O3 -std=c++17 $< -lgmpxx -lgmp -o $@

clean:
	rm -f build/*.aux build/*.log build/*.out
