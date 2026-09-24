# Slice regularity and the global inverse Fueter problem

One article assembled from **ten separately delivered manuscripts**, with the
duplicated mathematics stated once. [`MERGE_NOTES.md`](MERGE_NOTES.md) records
the provenance, the notation reconciliation, and the thirteen conflicts between
the sources that had to be resolved before they could be put in one document.

## What this is

The ten are not ten topics. One of them — `quaternionic_analysis.zip`, dated 20
September 2026 — is an expository survey, *Classical Complex Theorems over the
Quaternions*. The other **nine were all written on 21 September 2026 as
independent attempts at the same follow-up problem**, and one of them ships a
verbatim copy of the survey as its `source_context/`.

So the article has two parts by nature:

- **Part I** is the survey: slice regularity and Cauchy–Fueter regularity side
  by side, with Cauchy formulas, Taylor and Laurent expansions, maximum and
  minimum principles, the regular product and the geometry of zeros, the
  argument principle and Rouché, open mappings, Schwarz–Pick and an intrinsic
  Riemann mapping theorem.
- **Parts II–XI** are the global inverse Fueter problem: given an axially
  monogenic `g`, when is there a single-valued slice-regular `f` with
  `Δ₄f = g`?

## The answer, in one display

For `g = P + IQ` axially monogenic on the circularization of a planar domain,
form the two closed quaternion-valued one-forms

    ω_g = ½(−P dx + Q dy)
    θ_g = ½((xP + yQ) dx + (yP − xQ) dy)

A single-valued slice-regular primitive exists **exactly when both have
vanishing periods**; then `f(x+Iy) = (x+Iy)C + V` with `dC = ω_g`, `dV = θ_g`,
unique up to `q ↦ qa + b`. The monodromy is affine, the period pair
`(a_γ, b_γ)` is a complete obstruction, and the cokernel of the Fueter map has
real dimension `8m` where `m` counts the holes.

The point that the nine manuscripts exist to make is that **θ_g is computed
from the target**, with no first primitive chosen. The original survey's local
construction integrates one form and then a second form that depends on the
first primitive; the substitution `V = A − xB/y` removes that dependence, and
`η_C − d(xC) = θ_g` is the identity that connects the two.

## Nine independent derivations agreeing is the evidence

All nine reach the same two forms, the same criterion, the same affine
monodromy, the same `8m`, and the same leading constant in the logarithmic
energy law. They were written separately and they agree. That is worth more
than any one of them.

Where they *disagree* it is almost always notation, and `MERGE_NOTES.md` lists
all thirteen cases. Two were mathematical and would have produced a false
statement if the merge had been mechanical:

- **The size law at a critical singularity** has two different sharp constants
  in two different norms — the supremum over the whole conjugacy sphere, and
  the axial pair norm — and four manuscripts used the same symbol `M_g` for
  both. At `p = ι, a = 1, b = i` the constants are `2/π` and `√2/π`. The
  article uses different symbols and states both laws.
- **The conserved flux that recovers the slope residue** needs the weight
  `H_u = 3(Re q − u) + Im q`, not the naive `q − u`. The coefficient 3 is what
  makes the weight right-Fueter-regular: `Σ_μ ∂_μ(q−u)e_μ = −2`, whereas
  `Σ_μ ∂_μ H_u e_μ = 0`. A flux weighted by `q − u` is not conserved, so a
  merge that presented the moment formula as a computable flux would have been
  wrong.

## What is not proved

Both are stated in the article where they arise, and neither is hidden:

- The attribution of the arctangent / spherical Cauchy kernels is **left
  open**. The manuscripts cite two different papers as the primary source and
  the question cannot be settled from the manuscripts themselves; both are
  cited and the article says so.
- An editorial dispute about whether a published surjectivity statement is
  being corrected is recorded, not adjudicated.

These are AI-assisted research notes. None of the ten sources is refereed or
machine-checked, and this merge does not change that.

## Layout

- `article.pdf`, `article.tex` — the merged article.
- `MERGE_NOTES.md` — provenance, the notation table, the thirteen resolutions.
- `sources/` — all ten manuscripts verbatim, `NN-slug.tex`, with their original
  READMEs. Nothing was discarded.
- `code/` — the ten verification programs, `NN-slug.py`. They are independent
  implementations of overlapping checks; all ten were run and all ten pass.
  Their independence is the point, so all ten are kept.
- `data/` — the recorded outputs of those runs, `NN-slug-name.ext`.

## Running the verifiers

Each is standalone and needs only the standard library plus SymPy where noted:

```sh
for f in code/*.py; do python "$f"; done
```

They check the differential identities, the period formulas, the mode
normalizations, the residue-energy constants and the flux weights, numerically
and symbolically. They do not replace the proofs, and each says so in its own
output.
