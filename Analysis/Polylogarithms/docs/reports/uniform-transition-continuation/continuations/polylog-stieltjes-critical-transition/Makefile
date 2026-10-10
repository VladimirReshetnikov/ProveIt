.PHONY: all article exact numeric euler figures
all: article

article:
	python3 code/build_article.py

exact:
	python3 code/reproduce.py --suite exact

numeric:
	python3 code/reproduce.py --suite numeric

euler:
	python3 code/reproduce.py --suite euler

figures:
	python3 figures/plot_research_figures.py
