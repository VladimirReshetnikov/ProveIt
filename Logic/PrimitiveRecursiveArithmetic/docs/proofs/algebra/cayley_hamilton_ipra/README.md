# Cayley–Hamilton in intuitionistic primitive recursive arithmetic

Prepared for Vladimir Reshetnikov, 15 November 2026.

## Start here

- `cayley_hamilton_ipra.pdf` is the complete research manuscript.
- `cayley_hamilton_ipra.tex` and `sections/*.tex` are its complete LaTeX sources.
- `lean/FORMALIZATION_PLAN.md` is the detailed implementation and proof roadmap.
- `lean/NatKernelSpec.lean` explicitly defines the numerical checker.
- `lean/ObjectLanguageTargets.lean` gives the exact iPRA target and conditional
  native-calculus transfer.
- `lean/HostReference.lean` records separate Mathlib reference theorems.
- `code/verify_core.py` and `code/verify_trace.py` reproduce the finite checks.
- `verification/` contains actual run results and the delivery status.
- `sources/` records pinned repository provenance and source scope.

## Mathematical result

The manuscript gives a developed human proof that iPRA proves the uniform
primitive recursive identity `forall n, CHCheck(n) = 1`, where CHCheck tests
the coefficients of the characteristic polynomial evaluated at the generic
n by n matrix over integer polynomials. The determinant/adjugate proof uses
explicit finite reindexings and quantifier-free induction invariants.

Specialization gives Cayley–Hamilton over arbitrary commutative rings.
For each fixed primitive recursive ring presentation with internal proofs
of its laws, specialization is also an iPRA derivation. This is a schema
over fixed presentations, not quantification over all rings or a total
universal evaluator for all primitive recursive programs.

The coverage table lists 27 result families, including trace identities,
minimal polynomials, interpolation, module/integrality consequences,
quantitative matrix functions, and precisely specified quaternionic
extensions. Required units, field inverses, coordinate witnesses, splitting
data, and analytic moduli are stated where they are used.

## Formal verification status

**The Lean files are uncompiled specifications and an outline, not a completed
Lean proof of the iPRA theorem.** No Lean/Lake executable was available in the
delivery environment. Source interfaces were inspected at ProveIt commit
`73e6a339db7c72c6b13259059a8345b24385f6e3`, using Lean/Mathlib `v4.32.0`.

The concrete numerical `chCheck : Nat -> Nat` is defined, but construction of
its particular `chCheckCode : PR 1`, the internal representation lemmas, and
the final `Prf PRAAx [] ...` proof object remain to be implemented.
No `axiom` or `sorry` declaration is used to simulate that missing result.
Mathlib's existing Cayley–Hamilton theorem is explicitly kept separate.

## Reproduction

For the PDF, use a normal LaTeX installation with latexmk, pdfLaTeX, Latin
Modern, AMS packages, microtype, geometry, booktabs, longtable, enumitem,
listings, fancyhdr, xurl, and hyperref:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error cayley_hamilton_ipra.tex
```

For the exact checks, Python 3.10+ is sufficient; the core script additionally
requires SymPy (tested with 1.14.0). The trace script uses only the standard
library.

```sh
python3 -m pip install -r requirements.txt
python3 code/verify_core.py --output verification/core_results.json
python3 code/verify_trace.py
```

These are finite corroborating calculations, not an iPRA proof checker.
The core checks generic dimensions 0–4, 56 integer matrices, 180 modular
instances, 30 quaternion examples, exact counterexamples, and sample rational
tail estimates. The trace script checks 43 matrices, Newton/Bell/Hessenberg,
integer Faddeev–LeVerrier, truncated exp-log, and characteristics 2, 3, 5.

To develop the object-language Lean files, place them in a working checkout
of the pinned ProveIt project and follow `lean/FORMALIZATION_PLAN.md`.
`NatKernelSpec.lean` requires only `Std`; `HostReference.lean` requires Mathlib;
`ObjectLanguageTargets.lean` requires the ConciseIPRA library. Building the
outline files alone would still not prove the omitted main derivation.

## Scope boundaries

The general analytic-function discussion is replaced by explicit rational
Cauchy-code versions with finite tail bounds. Root finding, unrestricted
Jordan form, density of diagonalizable complex matrices, the broader Lie-group
examples, and the modified theorem for octonion matrices are not established.
The quadratic identity for one octonion is included. The report also documents
several missing hypotheses and displayed-formula defects in the source article.

The original proof exposition and code in this packet are newly written.
The cited upstream source files are not redistributed; their exact URLs and
Git blob hashes are retained in the source audit.

