# Spherical trigonometry and the tetrahedral cosine law in iPRA

This packet develops the principal identities of spherical trigonometry, and
the face-area/dihedral-angle cosine-law analogue for tetrahedra, in a form
suited to **intuitionistic primitive recursive arithmetic** (`iPRA`).

## Main deliverables

- `spherical_trigonometry_ipra.pdf` — 39-page human-readable report.
- `spherical_trigonometry_ipra.tex` and `sections/` — complete LaTeX source.
- `Lean/SphericalKernel.lean` — finite vector and polynomial kernel prototype.
- `Lean/SphericalTrig.lean` — abstract constructive spherical-trigonometry API.
- `Lean/IPRABridge.lean` — explicit `ConciseIPRA` representation boundary and
  object-language target signatures.
- `Lean/FORMALIZATION_PLAN.md` — dependency-ordered route to a completed Lean
  and `Prf PRAAx` formalization.
- `scripts/verify_identities.py` — exact symbolic generator checker.
- `artifacts/identity_ledger.json` — per-check residual ledger.
- `artifacts/verification_report.txt` — generated check summary.
- `coverage.csv` — theorem-family coverage and constructive side conditions.
- `SOURCES.md` and `sources/manifest.json` — external and repository sources.

## Mathematical scope

The report proves, for proper positively oriented spherical triangles:

- side and angle cosine laws;
- the spherical sine law;
- polar duality;
- half-angle, half-side, half-tangent and haversine formulas;
- Delambre–Gauss and Napier analogies;
- the spherical tangent law;
- cotangent/four-part, five-part and Cagnoli identities;
- all standard right and quadrantal triangle rules;
- differential variation formulas and a quantitative planar limit;
- Girard’s theorem, polygonal excess, solid-angle and L’Huilier formulas;
- constructive solution procedures for SSS, SAS, SSA, ASA, AAS, AAA and SSAA;
- the tetrahedral face-area cosine law and tetrahedral sine-product identity.

The finite checker verifies **68 exact generator identities in 14 families,
with zero failures**. It uses exact SymPy polynomial/rational arithmetic; it
performs no floating-point trigonometry or numerical sampling.

## Meaning of “in iPRA”

First-order `iPRA` has natural-number variables, not a primitive sort of all
real numbers. The report therefore uses a schema over fixed
primitive-recursive rapid dyadic names. Regularity, magnitude, orientation,
branch and apartness data are explicit certificates. Division is introduced
only from positive separation; square roots use bounded dyadic search; and
limit statements include primitive-recursive moduli.

The ambient Lean algebraic prototypes and the object-level arithmetic proof
are kept separate. A successful Mathlib `ring` proof does not by itself produce
`Prf PRAAx`. The final lowering path is stated explicitly in the report and in
`Lean/FORMALIZATION_PLAN.md`.

## Reproduce

Requirements for the exact checker are Python 3.11+ and SymPy. Requirements
for the PDF are a standard TeX Live installation with AMS, `mathtools`,
`booktabs`, `longtable`, `tabularx`, `multirow`, `enumitem`, `hyperref`,
`fancyhdr`, `listings`, `url`, and TikZ.

```bash
./build.sh
```

or separately:

```bash
python3 scripts/verify_identities.py
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  spherical_trigonometry_ipra.tex
```

The generated checker output is written to `artifacts/`.

## Lean status

The delivery environment did not contain Lean or Lake, so the `.lean` files
were not compiled here. They contain no `sorry` declarations and introduce no
custom axioms, but this is source inspection rather than kernel validation.
They are prototypes and interfaces, not a completed formal proof.

The intended environment is the ProveIt repository at commit
`a3c053cc6243dca44824510fac104958d616a6b9`, with Lean/Mathlib 4.32.0. Use the
commands and acceptance criteria in `Lean/FORMALIZATION_PLAN.md`.

Prepared for Vladimir Reshetnikov, 15 November 2026.
