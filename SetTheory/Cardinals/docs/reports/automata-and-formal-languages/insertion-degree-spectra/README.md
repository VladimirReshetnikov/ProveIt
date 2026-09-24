# Gaps in Bounded-Shuffle Hierarchies

Research note prepared for Vladimir Reshetnikov, 20 September 2026.

## Main results

The article gives a counterexample to the insertion-degree No-Gap Conjecture
stated in Charles E. Hughes, arXiv:2608.27755v1, Section 11. It then proves:

* Every finite set of positive integers containing 1 is the insertion-degree
  spectrum of two nonempty finite languages, over a suitable finite alphabet.
* Any prescribed finite list of insertion degrees greater than 1 can be realized
  by distinct exceptional outputs, with every other output having degree 1
  (Theorem 5.1).
* A ternary pair has spectrum {1,3}, with the sole difficult output `abcba`.
  Its output length 5 is the minimum possible length of any gap witness.
* A binary pair has spectrum {1,2,4}; all 18 singleton source-pair spectra
  are initial intervals. Thus source-pair ambiguity can erase an entire degree.
* The separate iteration-depth no-gap conjecture holds for arbitrary languages,
  by the shortest-prefix lemma.

The main parametric constructions have ordinary mathematical proofs independent
of any computation. The finite examples also have exact executable checks.
The unrestricted singleton insertion-degree conjecture is NOT resolved here.
There is no claim of proof-assistant checking or independent peer review.

## Files

`article.pdf` and `article.tex` are the paper and its complete source.
`tex/` contains the included LaTeX certificate tables.
`code/verify.py` verifies all small instances by two independent algorithms.
`code/make_search.py` generates optional SMT-LIB discovery experiments.
`data/verification.json` records the actual checks and sample sizes.
`data/*_degrees.csv` contains complete output-degree maps and optimal masks.
`data/*_pairs.csv` contains the degree histograms for every source pair.
`data/binary_erasure.csv` contains all 23 competing low-cost certificates.
`data/search_binary.smt2` is a free search for a binary counterexample.
`data/binary_fixed_model.smt2` pins the language pair used in the paper.
`SOURCES.md` records the primary sources and the literature-search boundary.

## Reproduce exact verification

Python 3.9 or newer; no third-party packages:

```text
python code/verify.py
```

The script uses exceptions for failed checks; it is not disabled by Python's
`-O` flag. It rewrites the CSV/JSON output in `data/` by default. For another
output directory:

```text
python code/verify.py --out new-results
```

The exact comparison includes all 243 ternary output words and all 128 binary
candidate output words, including nonmembers. It compares assignment-mask
exhaustion with a minimum-cost dynamic program for each source pair.
All family outputs are checked for r=2 and r=3. Larger instances are sampled;
this distinction is explicit in the JSON report and the paper.

## Compile the paper

Use a current TeX Live or MiKTeX installation with the packages in the preamble
(in particular newtx, amsthm, shuffle, microtype, booktabs, and hyperref):

```text
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

There is no BibTeX dependency: the bibliography is embedded.

## Optional discovery search

With an independently installed SMT-LIB solver such as Z3:

```text
z3 data/search_binary.smt2
z3 data/binary_fixed_model.smt2
```

Both should report `sat`. The free search may produce a different counterexample.
The fixed instance pins the verified six-word/three-word language pair.
No language-size optimality claim is made. A solver is not needed for any of
the verification commands above.

The source paper is not included in this archive. Its definitions and the
specific version consulted are identified in the article and SOURCES.md.
