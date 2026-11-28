.PHONY: all check clean
all:
	pdflatex -halt-on-error -interaction=nonstopmode paper.tex
	pdflatex -halt-on-error -interaction=nonstopmode paper.tex
check:
	python3 verify.py
	$(CXX) -O3 -std=c++17 verify_six.cpp -o verify_six
	./verify_six
clean:
	rm -f paper.aux paper.log paper.out verify_six
