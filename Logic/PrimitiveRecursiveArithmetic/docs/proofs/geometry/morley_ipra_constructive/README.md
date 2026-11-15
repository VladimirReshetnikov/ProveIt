# Morley's trisector theorem in iPRA

This archive gives a constructive, human-readable proof of Morley's trisector
theorem together with a precise arithmetic reading suitable for intuitionistic
primitive recursive arithmetic (`iPRA`).

## Main result

Because the language of arithmetic does not quantify over arbitrary real
points, the internal theorem is stated over finite exact certificates:

```text
iPRA proves: for every code w,
  MorleyCert(w) -> EquilateralSq(w).
```

A certificate uses one polynomial-quotient scalar representation, exact point
and direction coordinates, one-third rotation pairs, a common sine-law scale,
positive ray parameters, finite sign traces selecting the internal branches,
and explicit inverse witnesses for every canceled factor.  The conclusion is
equality of the three squared Morley-side lengths.

The ordinary theorem over Euclidean real triangles follows semantically from
the same universal algebraic derivation.  The arithmetic theorem itself ranges
only over finite codes; the paper explains this distinction in detail.

## Contents

- `morley_ipra.tex` - full source paper.
- `morley_ipra.pdf` - compiled 15-page paper.
- `MorleyAlgebra.lean` - candidate Mathlib algebra/vector kernel, with no proof
  placeholders or custom axioms.
- `MorleyIPRAOutline.lean` - module-by-module completion plan for the ProveIt
  `ConciseIPRA` development.
- `verify_morley_identities.py` - dependency-free exact sparse-polynomial
  checker.
- `morley_identity_certificate.json` - deterministic report for 18 checked
  identities.
- `morley_certificate_schema.json` - machine-readable certificate contract.
- `check_artifacts.sh` - reproducibility checks.
- `SOURCES.md` - source and revision notes.
- `verification_report.txt` - captured verification status.
- `pdf_preflight.json` - PDF structural preflight report.

## Proof architecture

The classical short trigonometric proof is retained as the readable spine, but
all analytic-looking primitives are eliminated:

1. A direction/angle is a unit pair `(c,s)`.
2. Angle addition is polynomial pair multiplication.
3. The sine law is replaced by a determinant identity.
4. The cosine law is replaced by a dot-product expansion.
5. The shifted triple-angle identity and the final Morley bracket are supplied
   as explicit ideal-membership certificates.
6. Squared distances avoid square roots.
7. Every cancellation uses a checked multiplicative inverse; sign traces are
   used only to certify that the selected rays are the internal trisectors.

The exact checker verifies 18 polynomial identities, including the two central
certificates, the 60-degree shift formulas, the algebraic angle-sum identity,
determinant extraction, and the squared-distance reduction.  It uses only
Python's standard library, exact `Fraction` coefficients, and a handwritten
sparse-polynomial implementation.

## Reproduce the checks

```bash
./check_artifacts.sh
```

Or separately:

```bash
python3 verify_morley_identities.py
python3 -m json.tool morley_identity_certificate.json >/dev/null
pdflatex -interaction=nonstopmode -halt-on-error morley_ipra.tex
pdflatex -interaction=nonstopmode -halt-on-error morley_ipra.tex
pdflatex -interaction=nonstopmode -halt-on-error morley_ipra.tex
```

The PDF was compiled with pdfTeX 1.40.26.  It was rendered and visually
inspected, and the supplied preflight report records 15 pages, no encryption,
and no structural warnings.

## Lean status

The delivery environment did not contain a Lean executable.  Therefore:

- the algebraic kernel file was reviewed and supplied as a concrete candidate,
  but not compiled here;
- the final `Prf PRAAx` theorem has not yet been entered;
- no completed Lean formalization is claimed.

`MorleyIPRAOutline.lean` gives a direct completion route: reflected sparse
polynomials, polynomial-quotient scalar certificates, exact geometry,
`PRAAx` derivability, and transfer through the existing native/iPRA
bi-interpretation.

## Repository pin

The ProveIt infrastructure was inspected at commit
`0bba41d70f061442357cae0f6de055434a33fb09` (15 November 2026 checkout date for
this archive).  See `SOURCES.md` for the exact references.
