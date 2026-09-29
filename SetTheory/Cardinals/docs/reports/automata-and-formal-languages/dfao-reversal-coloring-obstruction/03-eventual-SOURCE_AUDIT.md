# Source and proof audit

## Repository baseline

Repository: https://github.com/VladimirReshetnikov/ProveIt
Observed tree commit: 2cdcd74f3abcbbff7bd47c6c4265522395def609

Selected directory:
SetTheory/Cardinals/docs/reports/automata-and-formal-languages/dfao-reversal-coloring-obstruction/

Observed blobs:
- article.tex: e6dbd47babd24f1b086abf59bca372152bee06c3
- README.md: 13166e22098bf45e1bdcfaed4801dc83cd8dd16f

Read through the GitHub connector. The report proves a proposed binary
nonattainment result, develops collision-orbit graph bounds and certificates,
and reports 372 finite comparisons (7<=n<=30, 3<=k<n). It explicitly leaves
unrestricted exact optimality unresolved. It is not treated as formally
verified simply because it lives in ProveIt.

## Primary literature inspected

Sylvie Davies, State Complexity of Reversals of Deterministic Finite Automata
with Output, arXiv:1705.07150v2 (17 October 2017).

https://arxiv.org/abs/1705.07150
https://arxiv.org/html/1705.07150v2
https://arxiv.org/pdf/1705.07150v2

The article was inspected in HTML, and relevant PDF pages were rendered using
the web screenshot tool. In particular:
- Proposition 4 supplies the coloring-orbit interpretation.
- Section 3 defines U_(a,b), attributes its two-generation theorem, and gives
  the explicit generator used here.
- Section 5, printed page 17, distinguishes the nonattainment question from
  exact optimality of the binary lower bound for n>=7.

Markus Holzer and Barbara König, On deterministic finite automata and syntactic
monoid size, Theoretical Computer Science 327 (2004), 319-347.
DOI: 10.1016/j.tcs.2004.04.010.

Their Theorem 8 is the imported two-generator theorem, used in the form
explicitly quoted by Davies. The entire original 2004 proof was not
independently reconstructed. The generator is attributed through Davies
to B. Krawetz's 2003 University of Waterloo master's thesis; that thesis
was not read in full for this investigation.

## What is derived in this package

- A quantitative strict balancing inequality for complete-bipartite coloring
  counts, and the corresponding period-corrected minimum over coprime splits.
- An eventual structural exclusion argument for each fixed k, with the
  odd-k residual-vertex case handled by an explicit strictly positive margin.
- Eventual exact optimality of the closest-coprime split.
- An extremizer criterion, sharp constants, and residue recurrence laws.
- 919 exact finite graph-bound certificates and independent arithmetic checks.

The graph framework and U_(a,b) witnesses are reused, not claimed as new.
All needed graph, balancing, projection, and asymptotic steps are proved in
the article. The only substantial imported generation theorem is named.

## Evidence and non-evidence

Two programs agree on all 919 finite certificates. Their independence is
at the implementation level, not logical independence of the shared
mathematical certificate principle. Regression checks of formulas and
sampled automata are not proofs of universal statements. The infinite tail
proof does not rely on extrapolating the finite data.

No Lean/Rocq compilation or kernel audit was performed. No expert referee
has reviewed the manuscript. No explicit fixed-k threshold was established.
No uniform theorem for k growing with n is claimed.

The literature search was targeted to DFAO reversal and eventual/exact
optimality. It is not an exhaustive bibliographic review. Neither absence
of search results nor the old paper's open-problem wording establishes that
the problem remains unsolved in all later literature. Priority is unverified.
