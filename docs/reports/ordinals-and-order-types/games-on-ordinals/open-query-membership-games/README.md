# Open-query games on ordinal spaces

**An explicit negative answer to the topological-sum problem, with a finite Cantor–Bendixson classification.**

Research report dated 19 September 2026.

## Start here

Read `article.pdf` for the complete report. `article.tex` is its editable, self-contained LaTeX source. The bibliography is included directly in the source; no BibTeX run, remote assets, or data regeneration is needed to compile it.

The selected question is Problem 1.3 in Chiozini, Csernák, and Soukup, arXiv:2510.05754v3: does the set-membership number of a topological sum equal the supremum of the component values? The report gives a negative answer using two copies of the ordinal interval `[0, omega]`, whose separate values are 1 and whose sum has value 2.

The broader theorem computes the invariant for every nonempty Hausdorff space of finite Cantor–Bendixson height. If `h` is the index of the last nonempty derivative, the value is `ceil(log2(h+1))` when that derivative is a singleton, and `ceil(log2(h+2))` otherwise. The report includes explicit witnesses and complete proofs, rather than just computational evidence.

## Files

| Path | Contents |
|---|---|
| `article.pdf` | Finished research article, including proofs, bibliography, and proof audit. |
| `article.tex` | LaTeX source for the article. |
| `Makefile` | PDF build, exhaustive verification, and auxiliary-file cleanup. |
| `code/verify.py` | Standard-library Python verifier, strategy synthesis, and data generation. |
| `data/verification.json` | Machine-readable results of the full through-six-point run. |
| `data/verification.log` | Console output from that run. |
| `data/finite_poset_checks.csv` | Counts of posets and targets checked at each size. |
| `data/ordinal_values.csv` | Exact formula values for last derivative ranks 0 through 128. |
| `data/sharp_family.csv` | Sharp duplication examples for levels 1 through 16. |
| `data/strategy_certificate.json` | An explicit optimal three-query tree for two oppositely colored four-element chains. |
| `RESEARCH_STATUS.md` | Scope, source identification, and limitations of the claims. |

## Rebuild the PDF

Use a normal TeX Live or MiKTeX installation containing pdfLaTeX and the packages named in the preamble. Latin Modern is referenced as an installed TeX font; no font files are included in the archive.

From this directory:

```sh
make pdf
```

Without `make`, run the following command three times so that the table of contents and cross-references stabilize:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The final compilation used for this archive had no LaTeX warnings or overfull/underfull boxes. The PDF was rendered and inspected for layout problems.

## Reproduce the computation

Python 3.10 or later is sufficient; there are no third-party Python dependencies.

```sh
python3 code/verify.py --max-n 6
```

Equivalently, run `make verify`. This repeats **320,866 poset-and-target tests** on **5,231 naturally labelled posets** and rewrites the JSON/CSV results under `data/`. Runtime in the recorded environment was about 13 seconds, but runtime is machine-dependent. To regenerate a console log as well, use:

```sh
python3 code/verify.py --max-n 6 > data/verification.log
```

For a faster smoke test without replacing the included full-run data:

```sh
python3 code/verify.py --max-n 4 --output /tmp/ordinal-game-smoke
```

Without options the program checks through five points, not six. Do not use Python's `-O` option: verification assertions must remain enabled. The allowed upper limit of seven points is substantially more expensive; enumeration is exponential.

## What is checked

For every target in every enumerated poset, the script compares exhaustive minimax over all legal open questions, canonical alternating-closure profiles, and an alternating-chain dynamic program. It synthesizes a balanced query tree and checks its answers on every point.

These posets carry their **Alexandrov upper-set topology**. They are not finite Hausdorff approximations of ordinal spaces. The infinite-space theorems are established by the written proofs, not by the finite experiments.

A natural labelling means that every strict poset comparison runs from a smaller integer label to a larger one. Every finite poset admits such a labelling, so every isomorphism type through six points is covered, possibly more than once. The counts are not counts of unlabelled isomorphism classes.

The tables of ordinal values evaluate the proved formulae using exact integer arithmetic; they are not independent experiments on infinite topological spaces.

## Strategy certificate encoding

In `data/strategy_certificate.json`, bit `i` of a mask represents point `i`, with labels starting at zero. The strict-upper row at position `i` lists all points strictly above `i`. At an internal tree node, ask whether the point is in `open_mask`; follow `yes` or `no` accordingly. A leaf records the returned membership `color` and its closed-layer index. The supplied eight-point example has two disjoint four-element chains, profile `(5,5)`, and optimal depth 3.

## Research status

The counterexample directly refutes the question as printed in the retrieved v3. The report does not claim a resolution of all the paper's open questions, independent peer review, or proof-assistant formalization. No priority conclusion follows merely from not finding an earlier resolution. Classical difference-hierarchy machinery is explicitly credited in the article.
