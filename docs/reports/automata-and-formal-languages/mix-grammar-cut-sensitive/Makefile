PYTHON ?= python3
CXX ?= c++
CXXFLAGS ?= -O3 -std=c++17 -Wall -Wextra

.PHONY: all pdf check exhaust clean
all: pdf build/mix_exhaust

pdf: mix_grammar_report.tex
	pdflatex -interaction=nonstopmode -halt-on-error mix_grammar_report.tex
	pdflatex -interaction=nonstopmode -halt-on-error mix_grammar_report.tex
	pdflatex -interaction=nonstopmode -halt-on-error mix_grammar_report.tex

build/mix_exhaust: src/exhaust.cpp src/mix_parser.hpp
	mkdir -p build
	$(CXX) $(CXXFLAGS) src/exhaust.cpp -o $@

check: build/mix_exhaust
	$(PYTHON) tests/forward_oracle.py
	$(PYTHON) tests/test_results.py
	$(PYTHON) tests/check_recorded_results.py
	$(PYTHON) src/check_certificate.py certificates/separation_m1.json
	$(PYTHON) src/check_certificate.py certificates/separation_m2.json
	$(PYTHON) src/check_certificate.py certificates/separation_m5.json
	@test "`build/mix_exhaust --check 2 aaabbbcbbccccaa`" = "false"
	@test "`build/mix_exhaust --check 3 aaabbbcbbccccaa`" = "true"
	@test "`build/mix_exhaust --check 3 a accb b`" = "false"

exhaust: build/mix_exhaust
	build/mix_exhaust 7 > data/reproduced_cpp_through21.json

clean:
	rm -rf build
	rm -f mix_grammar_report.aux mix_grammar_report.log mix_grammar_report.out mix_grammar_report.toc
