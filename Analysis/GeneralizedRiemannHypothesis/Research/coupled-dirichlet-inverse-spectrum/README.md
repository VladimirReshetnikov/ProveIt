# Recovering the characters and the graph from a coupled Dirichlet spectrum

Read **paper.pdf** for the statements, proof, numerical example, and source comparisons. **paper.tex** is the entry point and uses the companion TeX files in this directory. The observation theorems about critical-line ordinates invoke the Dirichlet GRH theorem cited by the ProveIt article. The manuscript also gives an unconditional equal-size theorem for observation of the full complex zero divisor.

## Rebuild

From this directory, run the following with a standard TeX Live installation.

    pdflatex -halt-on-error paper.tex
    pdflatex -halt-on-error paper.tex

For reference resolution a third pass is harmless. The bibliography is embedded.

## Reproduce the examples

    python3 checks/exact_locator.py
    python3 checks/dirichlet_locator.py
    python3 checks/cycle_traces.py

The first script needs SymPy and works over the rational numbers. It checks the error-locator equations by polynomial divisibility, including a false extra copy of a genuine root. The second needs mpmath and evaluates completed Dirichlet functions for real quadratic characters of conductors 3 and 5 at 45 decimal digits. It searches for sign changes and refines nine sample roots. The third script uses SymPy to verify the signed-cycle principal-minor example for three through eight vertices. Recorded output is in the three JSON files alongside the scripts. Floating-point counts and roots are illustrative. The analytic proofs are in the manuscript.

## Source and scope

The project snapshot is VladimirReshetnikov/ProveIt at revision 00cadb961bbe77c74e5d082c4948f8884d58a970. Under Analysis/GeneralizedRiemannHypothesis, the project README describes the merger of 184 reports and the placement of a further 10 packets. The Article README describes an 851-page synthesis. The pertinent mathematical source is Article/sections/zer.tex, especially the final open question and the section containing zer:thm:tailrigid and zer:thm:window. Article/sections/src.tex states the Dirichlet critical-line theorem, pinned upstream at lsernau/grh-lean revision 72fead102f663d5c7a407964a13dc0cf9d977207.

The article supplies the Hermitian forward determinant, its count comparison, and inverse recovery for a known same-parity list. Article/sections/rec.tex, at rec:thm:primefreq and rec:thm:operatorinverse, also treats prime-frequency observations for a scalar differential polynomial applied to one completion. The present results concern an unknown multiset of labels and a Hermitian matrix coupling their completions. Bibliographic context and the precise scope of each assertion appear in the paper. The archive includes no new Lean formalization.

The three article sources in the pinned Git tree have the following blob IDs.

| File below Article/sections | Git blob |
| --- | --- |
| src.tex | f69668b2f95261630bb1282c2cc1f9c172b7e530 |
| zer.tex | d6802a5f06e094e395acd41edd5f9d24e440cf0b |
| rec.tex | 691e6509f9b2d3fff8d58968d3d4fd42cee72e1d |
