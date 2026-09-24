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
  (satellite work on the 1980 Theorem 5) uses 76 operations; see
  `Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md`.

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

## Provenance

This project was developed separately and moved into ProveIt on
24 September 2026: its `current/` directory became `Papers/` and its
`lean/` directory became `Lean/`. The standalone Lake package was dropped;
the vendored twelve-module extraction of ProveIt's `PAListCoding` was
replaced by the original library in `Logic/PeanoArithmetic/ListCoding/Lean/`,
whose exact-iteration block was split out of `TetrationDiophantine` into the
new module `PAListCoding.ExactTrace` so that this library does not import
Foundation.
The journal scans and their raw Mathpix OCR (cited by the editorial notes as
`original/<year>/…`) and the standalone MRDP extraction are not
included. Dated records in the notes and
in `Lean/STATUS.md` describe the earlier layout.
