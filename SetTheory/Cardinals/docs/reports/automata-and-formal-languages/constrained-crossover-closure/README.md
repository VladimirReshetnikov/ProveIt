# Aligned Fragments and Constrained Crossover

**Undecidability, exact generation depth, and rational growth of context-free recombination closures**

Research draft prepared with ChatGPT for Vladimir Reshetnikov, 29 September 2026.

## Read the article

`article.pdf` is the complete 23-page article. `article.tex` is its standalone
LaTeX source with an internal bibliography. The PDF includes complete proofs,
a source/status discussion, nine research questions, and a Lean development
plan. No repository checkout is required to compile or test this package.

## Main results

For constrained one-point crossover, parents have equal total length and
exchange suffixes at the same cut. Both endpoint cuts are permitted.

* Deciding `L crossover L = L` for a context-free grammar is co-r.e.-complete,
  already over the fixed alphabet `{0,1,@}`. The guard construction actually
  has a universal first generation for every input grammar.
* Eventual finite stabilization is undecidable over `{0,1,@,#}`. If `w=00x`
  is an omitted block, `r` copies separated by `#` have exact aligned-fragment
  rank `r+1`. This supplies witnesses at every stage on the nonuniversal side.
* The intrinsic rank contracts exactly by `ceil(rank/2)` under one parallel
  self-crossover generation. Parallel depth is `ceil(log2(rank))`; with one
  parent frozen in the seed it is `rank-1`. Both stabilization problems detect
  boundedness of the same rank.
* Finite-state inputs admit a polynomial-time DFA one-step test and a
  PSPACE-complete NFA one-step problem. Finite stabilization is decidable by
  an explicit reduction to distance-automaton limitedness; the stated
  EXPSPACE upper bound for DFA input is not claimed optimal.
* Every context-free seed's full closure has an effectively rational
  generating function, even retaining commuting letter weights. This does
  not imply that the closure language is context-free.
* An explicit binary linear context-free seed S_q has a non-context-free
  closure with counts `4^floor(n/q)`. Its parallel generation k has minimal
  eventual recurrence order `q*2^k+1`; the corresponding frozen-source order
  is `q*(k+1)+1`.

The first result answers the specific question on printed page 3 of Charles
E. Hughes, arXiv:2608.27755v1. The relationship to ProveIt's insertion-spectrum
report and the exact inspected revision are given in the article and
`notes/provenance.md`. This package does not solve the both-singleton insertion
conjecture and does not duplicate the repository's binary insertion-profile
construction.

## Mathematical status

This is an unrefereed draft, not a proof-assistant development. The article
separates its arguments from classical inputs: CFG universality, effective
Parikh semilinearity, Presburger counting, and distance-automaton limitedness.
The limited literature search is not an exhaustive priority claim.

The finite computations are audits, not proofs of the universal statements.
They do not implement a general CFG compiler, a Presburger counting engine,
or a limitedness decision procedure.

## Reproduce the exact audit

Python 3.10 or later, standard library only:

```sh
python3 code/verify.py
```

The delivered run passed **1,766,639 explicit checks**. It includes
all **65,814** binary seed sets at lengths
0 through 4, all 64 complete two-state binary DFAs with fixed initial state,
independent full-alphabet block checks, and exact rank/count/recurrence audits
for the linear-seed family. See `data/verification.json` for the detailed
scope and `data/verification.txt` for captured console output.

The program overwrites `data/verification.json`; a different runtime changes
its elapsed-time field but not the mathematical counts. Checks remain active
under `python -O`. Only elapsed time uses floating point.

## Rebuild the PDF

A TeX Live or MiKTeX installation with the packages named in the preamble is
required, including `newtxtext` and `newtxmath`.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively run `pdflatex` three times. `make pdf`, `make check`, and
`make clean` provide shortcuts. No font files are included.

## Package contents

- `article.tex`, `article.pdf`: source and typeset article.
- `code/verify.py`: exact finite reference verifier and reusable rank routines.
- `data/verification.json`, `data/verification.txt`: executed audit receipts.
- `notes/provenance.md`: source versions, repository scope, and novelty limits.
- `notes/proof-audit.md`: mathematical edge cases and proof-dependency audit.
- `Makefile`: PDF and verification commands.
