# Hilbert's tenth problem: Jones's articles on Diophantine representation

Corrected editions and a Lean 4 formalization of six articles on Hilbert's
tenth problem, Diophantine representation of recursively enumerable sets and
universal Diophantine equations by James P. Jones and coauthors:

| Year | Authors | Title | Journal | Engine |
|---|---|---|---|---|
| 1974 | J. P. Jones | Recursive Undecidability—An Exposition | *Amer. Math. Monthly* 81, 724–738 | pdfLaTeX |
| 1976 | J. P. Jones, D. Sato, H. Wada, D. Wiens | Diophantine Representation of the Set of Prime Numbers | *Amer. Math. Monthly* 83, 449–464 | pdfLaTeX |
| 1978 | J. P. Jones | Three Universal Representations of Recursively Enumerable Sets | *J. Symbolic Logic* 43, 335–351 | LuaLaTeX |
| 1980 | J. P. Jones | Undecidable Diophantine Equations | *Bull. Amer. Math. Soc. (N.S.)* 3, 859–862 | pdfLaTeX |
| 1982 | J. P. Jones | Universal Diophantine Equation | *J. Symbolic Logic* 47, 549–571 | XeLaTeX |
| 1984 | J. P. Jones, Yu. V. Matiyasevich | Register Machine Proof of the Theorem on Exponential Diophantine Representation of Enumerable Sets | *J. Symbolic Logic* 49, 818–829 | pdfLaTeX |

## Layout

- [`Papers/`](Papers/README.md): the corrected editions
  (`<year>/jones<year>_corrected.tex` and `.pdf`), each with its consolidated
  editorial notes (`<year>/jones<year>_editorial_notes.md`: every discrepancy
  between a naive OCR reading of the printed article and the edition, with its
  classification and justification), the dated log of revisions and checks
  `EDITORIAL_NOTES.md`, the satellite article on the operation count of the
  1980 Theorem 5 (`1980/jones1980_theorem5_operations.pdf`) with its proofs
  and explorations, and the verification programs in `verification/`.
- [`Lean/`](Lean/README.md): the Lean 4 / Mathlib formalization, the library
  `Diophantine` of the root Lake workspace, with its status register
  [`STATUS.md`](Lean/STATUS.md), the [MRDP guide](Lean/MRDP.md) and the axiom
  audits in `Lean/checks/`.

## Highlights

- **MRDP in both directions.** `Diophantine.mrdp`: every recursively
  enumerable set of naturals is the projection of the natural zero set of one
  integer polynomial with finitely many witnesses, including input zero;
  `Diophantine.mrdp_iff` proves the converse, and `Diophantine.mrdp_dioph_iff`
  states it through Mathlib's `Dioph`.
- **The universal pair `(58, 4)`** of the 1980 and 1982 articles on positive
  inputs, from the complete (D1)–(D37) system of 1982 §5; the three printed
  1982 systems represent every r.e. set with 12, 14 and 28 positive witnesses.
- **Prime-representing polynomials** of 1976: an integer polynomial on twelve
  natural coordinates whose positive values are exactly the primes, and one of
  exact degree 13697; the 87-operation primality certificate.
- The 1974 exposition (Busy Beaver functions on ProveIt's machine model), the
  1978 Bounded Quantifier Theorem and Divisor Lemma, and the 1984
  register-machine encoding.
- The formalization introduces no axioms and no `sorry`; transitive axiom
  audits are in `Lean/checks/`. Coverage per article and the statements still
  open are in [`Lean/STATUS.md`](Lean/STATUS.md).
- The editorial review found and corrected errors in the printed articles;
  every correction is justified in the per-article notes.
- The smallest established complete universal straight-line certificate
  (satellite work on the 1980 Theorem 5) uses **75 operations (41 multiplications and34 additions/subtractions)**,
  with30 positive witnesses and19 equations; see
  [the complete proof](Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md).
  Three independent integration reviews and focused source/component checks
  pass. The [signed-projection refinement](Papers/research-wip/native-stream-queue/complete75_signed_projection_elimination101.md)
  retains75 operations with **20 positive witnesses and nine equations**.
  Its degree-84 polynomial is evaluable in **101=50M+51A operations**, with
  fixed compiler numerals and ordinary input. Conditional positivity is
  proved on the zero set; every original positive solution is preserved.
  The newer [bounded-projection polynomial](Papers/research-wip/native-stream-queue/complete75_bounded_projection_elimination99.md)
  costs **99=49M+50A**, with **19 positive witnesses** and degree84.
  Its comparison system costs76 with eight equations; a proved canonical
  compiler margin preserves the same accepted ordinary inputs.
  The [positive Pell-root coordinate](Papers/research-wip/native-stream-queue/complete75_positive_root89.md)
  gives **89=47M+42A**, with the same19 positive witnesses and exact
  degree148. It is bijective on positive solutions with the
  [reversed auxiliary degree160 source](Papers/research-wip/native-stream-queue/complete75_reversed_auxiliary89.md).
  Integer unit obstructions, displaced Pell indices and the new root-gap
  positivity proof justify the unsquared product. Its comparison circuit costs88.
  The [positive-root partitions](Papers/research-wip/native-stream-queue/complete75_positive_root_degree_tradeoffs.md)
  give **94 operations at degree84**, **93 at degree118**, and **92 at degree122**.
  In particular the degree84 option improves its preceding96-operation bound.
  The [coupled index/linear product](Papers/research-wip/native-stream-queue/complete75_coupled_index_linear88.md)
  now gives **88=47M+41A**, with **19 positive witnesses** and exact degree151.
  Sharing k-hE removes one subtraction; the compiler masks exclude the
  remaining negative sign through a population-count contradiction.
  Its positive zero set equals the89 source's under the full compiler contract.
  Its [grouped variants](Papers/research-wip/native-stream-queue/complete75_coupled88_degree_tradeoffs.md)
  give **91 operations at degree130** and **93 at degree90**, retaining the
  full strong equation and the same positive zero set. The93/90 option
  supersedes93/118;92/122 and94/84 remain distinct.
  The75 comparison bound,88 polynomial bound and89/148 tradeoff are distinct.
  These optimized results are not yet Lean formalized.
- A [group-commutator substrate](Papers/research-wip/native-stream-queue/group_commutator_universal_substrate.md)
  represents every computably enumerable positive set by membership in a
  finitely generated SL(4,Z) subgroup, with a fixed quadratic ordinary-input
  curve costing five scalar operations. One fixed universal subgroup serves
  all programs with a six-operation program/input loader. The group embedding
  theorem is cited explicitly; a uniform Diophantine certificate for arbitrary
  selected matrix products remains open. This is a substrate result, not a smaller
  complete universal equation. The [four-register history interface](Papers/research-wip/native-stream-queue/group_four_register_history.md)
  reduces the evolving matrix data from eight entries to four bounded
  registers, with a paid10-operation input boundary and conditional43-operation
  aggregate. Digit selection, typing, control and power geometry remain unpaid.
- The [Heisenberg audit](Papers/research-wip/native-stream-queue/heisenberg_two_generator_membership.md)
  gives a uniform four-positive-witness certificate for two fixed generators
  in H^r, at18r+10 graph operations or27r+12 polynomial operations and degree
  at most4. That whole family is decidable. Explicit three-letter targets
  show that pair counts and weighted-triangle bounds do not enforce order.

## Building and checking

From the ProveIt root (one build at a time, as the repository guidance
requires):

```powershell
$env:LAKE_JOBS = '1'; $env:LEAN_NUM_THREADS = '2'
lake build Diophantine
lake env lean Computability/HilbertTenthProblem/Lean/checks/MRDPAxioms.lean
```

Rebuild an edition with its engine, two passes, in `Papers/<year>/`; run a
checker with, for example,

```powershell
$env:PYTHONUTF8 = '1'; py Computability/HilbertTenthProblem/Papers/verification/round4_1984_checks.py
```

## Scope

The editorial notes compare each edition with the journal scan and its raw
Mathpix OCR, which they cite as `original/<year>/jones<year>.pdf` and
`original/<year>/jones<year>.tex`; these inputs are not included. The Lean
library uses ProveIt's `PAListCoding` for finite traces; its module
`PAListCoding.ExactTrace` keeps the Foundation library out of this
library's imports. Dated records in the editorial log and in
`Lean/STATUS.md` cite files by an earlier layout: `lean/` is `Lean/`,
`current/` is `Papers/`, and `vendor/pa-list-coding` is `PAListCoding`.
