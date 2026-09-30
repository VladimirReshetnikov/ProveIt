# Verification and dependency status

## Executed checks

`python code/run_checks.py` passed 32,418 exact-arithmetic assertions with seed
20260930. The detailed per-category counts are in `check_results.json`.
The tests include 12 seeded random instruments, an explicit interference
example, elementary and bounded-height searched Gram factors, and complete
canonical polynomial assignments. Arithmetic uses integers and exact fractions.

The small D=2, K=2, n=2 polynomial was expanded into 647 monomials and checked
against its residual-sum evaluator. The D=4, K=7, n=3 certificate was checked
as 264 residuals with 245 natural witnesses. Increasing any single witness
coordinate of the supplied zero-word assignment by one was rejected.

Finite test coverage supports implementation consistency. It is not the proof
of the general construction or the imported undecidability theorem.

## Mathematical proofs in the manuscript

The manuscript gives proofs of rational Gram factor consequences, row packing,
mortality equivalence, one-step witness extension, the all-word block invariant,
canonical bounded-history quartics, probability separation, and the stated
reductions and corollaries. These proofs have not been checked by Lean or a
second independent proof assistant.

The d+3 row argument uses the classical Meyer theorem. The independent 4d row
route uses Lagrange's four-square theorem. The dimension-four hardness result
uses Neary's published six-generator, 3-by-3 matrix-mortality result (STACS 2015,
Corollary 12). The unbounded Diophantine conclusion uses MRDP.

The 2012 benchmark compared in the article is the explicit dimension-fifteen,
nine-outcome construction of Eisert, Mueller, and Gogolin. The literature search
was targeted, not exhaustive; global priority or optimality is not certified.

## ProveIt inspection

The MRDP guide and actual Diophantine trace-module source were read at commit
f608f1cb3c5be8a736df1328c01b293aabfccf4e. No repository build was performed, no
new Lean proof file is supplied, and no remote repository state was changed.

## Document checks

The final manuscript was compiled with pdfLaTeX through latexmk, producing a
22-page PDF. All pages were rendered with Poppler and inspected in contact
sheets; principal theorem, count, and reference pages were also checked at
larger size. The final build has no overfull boxes or unresolved references.
