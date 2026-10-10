.PHONY: all paper check quick clean
all: paper check
paper:
	./build.sh
check:
	python3 code/verify.py
	python3 code/check_lattice.py
quick:
	python3 code/verify.py --quick --output results/quick
clean:
	rm -f paper.aux paper.log paper.out paper.toc paper.bbl paper.blg
