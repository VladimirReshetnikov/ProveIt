# Sources, repository delta, and verification boundary

## Pinned repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected snapshot: `1156651a9417231a9a54442b420f099ee85ae7fe`.
The snapshot was read, not modified or rebuilt. The article is dated
30 September 2026 (the snapshot timestamp is 1 October in UTC).

Relevant report directory:
`SetTheory/Cardinals/docs/reports/galois-theory-and-radicals/sextic-block-resolvent-separators/`

- `article.tex`, Git blob `efcff1403f3ea21e3925042a8618a18e4df847b5`.
- `README.md`, Git blob `54d7469ae1ce9d626d8c6f7fac8de3c153a75637`.
- Formal endpoint:
  `Algebra/PolynomialFormulas/Lean/PolynomialFormulas/SexticRadicalDecision.lean`,
  Git blob `c19d91c580fe01ea6244e0b37b72878cbaa9e349`.

The report's Part II is the predecessor titled *Three Plus One:
Radical-Solvability Tests Without Separating Sextic Resolvents*.
Relevant questions are in its merged Section 30:

| Predecessor question | Result in this article |
| --- | --- |
| 30.1: existence of a nonzero nonsolvable exception | Remains unresolved. |
| 30.2: fewer matching tests | A selected single parameter, zero, is safe for the compressed resolvent. Two arbitrary distinct parameters suffice. |
| 30.3: can the exceptional polynomial have degree two? | No: affine rank is at least two, so its degree is at most one. |
| 30.5: recover block witnesses | Not solved; the degree-36 example illustrates the distinction. |
| 30.6: smaller structured coefficient realizations | Partial answer: 15-dimensional cubic matrix polynomial and 20-dimensional Pfaffian. No minimal linear-pencil claim. |
| 30.8: formalization | A dependency plan only; no new Lean/Rocq proof. |

Inherited facts are explicitly reproved: the solvable block criterion,
invariant-graph rigidity, shifted pair-product/triple safety, pentad incidence,
shared-edge factorization, and rational-fiber classification. The new ring
certificate and affine-rank argument are not assumed from the predecessor.

## External primary sources

1. C. Boswell and M. L. Glasser, *Solvable Sextic Equations*, 2005,
   arXiv:math-ph/0504001. https://arxiv.org/pdf/math-ph/0504001
   The PDF and its displayed invariant on printed page 3 were inspected.
   Its matching invariant is `e6 * A_P` after relabeling. Thus the underlying
   invariant and the general two-resolvent framework are classical. Its
   triple invariant differs from this article's `b_T`.
2. M. Wimmer, *Efficient numerical computation of the Pfaffian for dense and
   banded skew-symmetric matrices*, ACM Transactions on Mathematical Software
   38, article 30 (2012); arXiv:1102.3440.
   https://arxiv.org/abs/1102.3440
   Source for the established Pfaffian computational context; the supplied
   small rational-elimination implementation is written for this package.
3. SymPy 1.14.0 number-field documentation:
   https://docs.sympy.org/latest/modules/polys/numberfields.html
4. SymPy 1.14.0 Galois test source:
   https://github.com/sympy/sympy/blob/1.14.0/sympy/polys/numberfields/tests/test_galoisgroups.py
   Read from the installed distribution. Its 16 degree-six seed polynomials
   were transcribed into `code/verify.py`; additional affine variants are
   generated there. Software and seed-file hashes are recorded separately.

## Mathematical and computational non-claims

The article is an unrefereed, AI-assisted mathematical manuscript. The proofs
are written proofs. The exact identity checkers and regression tests do not
confer proof-assistant verification on the group-theoretic conclusions.
Historical priority for the proposed extensions is not established.

No general sextic radical-construction algorithm, optimal test count,
production speed advantage, classification of exceptional sextics, or
nonzero nonsolvable false-positive example is claimed. A rational value of
the matching invariant need not identify a Galois-fixed matching. The
original bivariate descriptor curve still collapses at zero; the safe result
is about its compressed resolvent, not the collapsed curve evaluation.
