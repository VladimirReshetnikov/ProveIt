# Research status

## Proved in the article

| Result | Location | Status |
|---|---|---|
| Exact even-span periods for arbitrary complex iterated derivatives | Lemma 4.1 | Product identity, valid at zeros and repeated cube vertices |
| Sharp rank-one energy cap on a fixed derivative | Theorem 4.3 | Full proof, every dimension and every m >= 2 |
| M(C_d) = 1 - (d+1)/2^d | Theorem 1.1 / Section 5 | Full proof for every d >= 3, n >= 2, arbitrary bounded f |
| Quartic stabilization under adjoining inactive coordinates | Section 5.3 | Resolves prior draft's Research Question 1 |
| Pure defects iff canonical obstruction modulo an integrable tensor | Theorem 6.4 | Full algebraic proof for d >= 4 |
| One-dimensional defect image reduces tensor to two active coordinates | Theorem 6.5 | Full proof; does NOT assert optimizer descent |
| Non-pure symmetric trilinear support >= 7/32 | Theorem 7.7 | Full proof for vector-valued maps; sharp |
| Non-pure s-linear support >= 7/2^(s+2), s >= 3 | Theorem 7.8 | Full proof; optimality not claimed beyond s = 3 |
| Exact universal symmetric thresholds through degree six | Theorem 1.2 / Section 8 | Full proof; endpoint witnesses C_d, f = 1 |
| All-degree universal upper bound 1 - min(d+1,7)/2^d | Theorem 1.2 | Full proof; exactness asserted only through degree six |
| Nonnegative deficit recursion | Proposition 9.1 | Exact identity and necessary near-extremizer estimates |
| Corrupted-selector and approximate-period margins | Proposition 9.2 and Lemma 9.3 | Full proofs under stated model/error hypotheses |

The full proofs of the required nonclassical integration and spectral shear
background are included and credited. Those background results are not
claimed as new.

## Verification performed

- The standard-library verifier completed successfully using exact arithmetic.
- Formal cube monomials were checked with separate conjugated and unconjugated
  exponents; no cancellation by a possibly zero function value was used.
- Integer differences modulo powers of two checked the explicit primitives.
- The binary trilinear census and vector-valued extensions were checked
  exhaustively in the stated finite cases.
- Exact energy and slicing computations included Gaussian-rational amplitudes
  and zero values.
- The PDF was compiled from the supplied source, checked for unresolved
  references and overfull boxes, rendered, and visually reviewed.

These are consistency checks, not a substitute for the proofs. No Lean build
or independent referee review was performed.

## Not proved or claimed

- The universal canonical formula in degrees >= 7.
- A full classification of quintic/sextic endpoint tensors or phases.
- A general theorem that pullback along a quotient preserves M(T).
- Multiplicativity under direct sums outside the previously known cubic case.
- The corresponding mixed-function or odd-characteristic sharp bounds.
- Automatic construction of a symmetric multilinear selector from large
  Gowers norm, or elimination of arbitrary multiaffine lower-order terms.
- A boundary-free local-domain version or a new end-to-end Szemerédi bound.
- Historical first priority for the mathematical statements.

## First remaining numerical gap

For every n >= 2:

    120/128 <= M_sym(7,n) <= 121/128.

The upper bound is proved; equality with the lower endpoint remains a
proposed research question. For d >= 7 the displayed upper/lower gap in this
paper is (d-6)/2^d.
