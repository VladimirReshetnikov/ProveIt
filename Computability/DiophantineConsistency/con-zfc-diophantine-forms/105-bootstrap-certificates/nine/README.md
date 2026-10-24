# A short local Laurent majorant for nine-positive Con(ZFC) equations

This package gives two explicit nine-positive-variable polynomials with the same
existential source interpretation as their pinned saturated-Pell parents.

| Circuit | Positive unknowns | Live binary operations | Exact degree | Complete coefficient tuple |
|---|---:|---:|---:|---|
| `equations/compact2082.json` | 9 | **442** | **1,520,186** | compact54-sharp |
| `equations/h1868.json` | 9 | **456** | **1,376,378** | original31 |

The 456-operation polynomial improves the reviewed 475-operation,
degree-1,379,730 nine-positive point in both operations and degree. The
442-operation polynomial trades nine additional operations against the current
433-operation, degree-1,628,768 target for a degree reduction of 108,582.
Neither reduces the number of variables. These are useful additional tradeoffs,
not a global simplicity or historical-priority claim.

The new ingredient has only **eight monomials**. Put

```
J = 4A-5, D = 1+(A^2-1)C^2,
F = 1+(A^2-1)D(iJC^2)^2,
T = iC^2[AJ(2D-C^2)+3C^2-4].
```

For every A>=2, C>=2, i>=1, the package proves `T > 2 sqrt(DF)`.
Use `V1=TGH` and `a1=4DFI` in the existing positivity-first norm finalizer.
Replacing the positive carrier input by `C=c+1` makes the new bound unconditional
before any equation is assumed. Canonical source witnesses already satisfy C>1,
so the restriction preserves existential completeness. The restriction is essential:
at A=3,C=1,i=1 the local defect equals -308.

Every equation file is a division-free arithmetic DAG containing only literal
integers, nine variables, the explicitly supplied fixed integer leaves, and binary
addition, subtraction and multiplication. Named registers are abbreviations and do
not add variables. All fixed leaves are supplied as exact signed binary numerals
under `fixed/`; the complete four-port tuples under `ports/` independently reconstruct
them. No external filesystem path, program index, or undefined constant is needed
to evaluate the polynomials.

## Reproduce

Only Python 3.10+ and the standard library are required.

```sh
python3 verify.py
python3 -O verify.py
python3 build.py --output /path/to/new-output-directory
```

`verify.py` does not import the builder. It checks every fixed numeral, exact
local and outer norm identities, the complete structural source-prefix maps,
all new register formulas, all live operations, a cancellation-resolved exact
degree certificate, and deterministic full reconstruction. It also rejects two
negative controls. The normal and optimized receipts are identical.

`PROOF.md` supplies the unbounded argument, and `notes.tex` is a TeX-ready version
of the new lemma and composition. `SOURCE_PINS.json` pins the copied parent
artifacts to ProveIt snapshot `8f8fac484b976ba0ab75fd173282e838ca5a3b85` and the
original saturated-certificates arrival. Relevant inherited ordinary proofs,
coefficient bindings, and license notices are retained.

The newly proved result is a complete existential reduction to the exact inherited
source. Composing it with the parents' named native/compiler/refutation calibration
gives the intended equivalence with Con(ZFC), without assuming consistency or
inconsistency. This package supplies no new Lean/Rocq certificate or encoded
object-ZFC derivation. Finite artifact checks do not replace the retained unbounded
calibration proofs. The new local lemma and semantic transplant received a separate
AI-assisted mathematical review, recorded in `REVIEW.md`.
