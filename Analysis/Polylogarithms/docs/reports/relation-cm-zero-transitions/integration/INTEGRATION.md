# Integration into the ProveIt manuscript

Baseline commit: `9bc738d3be22b8586a24693f19fb2e2a50ecd1bf`.

All paths in the first column below are relative to this continuation
package. Target chapter paths are relative to
`Analysis/Polylogarithms/docs/manuscript/` in ProveIt.

## Section placement

| Continuation source | Proposed manuscript location | Integration action |
|---|---|---|
| `sections/02_relation_lattices.tex` | `chapters/05-signed-kernels.tex`, after the formal matrix definition | Replace the odd-weight rank conjecture with the new theorem and proof; retain the historical finite receipt as validation. |
| `sections/03_mixed_identity.tex` | Same chapter, after the rank theorem or next to mixed-color evaluations | Add the all-even-weight trailing-one identity and explicit integer row certificate. |
| `sections/04_cm_products.tex` | `chapters/06-cm.tex`, after the empirical class-product catalogue | Add the normalized theorem, phase discussion, exact class-polynomial data, and proofs of the five products. |
| `sections/04a_modular_polynomials.tex` | Within the new CM product section | Preserve the exact generator and valence-bound certificate. Update its `input` path after relocating it. |
| `sections/04b_cm_genus.tex` | CM chapter, following the norm theorem | Prove the three recorded ratios and add weight-six genus evaluations. |
| `sections/04c_cm_genus_closure.tex` | Within the genus section, before its final research directions | Add the fixed-field degree theorem and quadratic closure for the three worked discriminants. |
| `sections/05_zero_preliminaries.tex` | Usually omit when integrating | This repeats the established baseline global theorem to make the standalone article self-contained. Redirect its references to the existing zero chapter. |
| `sections/06_classical_zeros.tex` | `chapters/09-zero-certificates.tex` or after its low-index certificates | Add count monotonicity, classical lower bounds, and the exact fifth-index transition. |
| `sections/07_lerch_bifurcations.tex` | `chapters/09-zero-geometry.tex`, after the family definition and global bound | Add the small-parameter classification, alternating motion, and fold theorem. |
| `sections/08_corrections_and_questions.tex` | Distribute corrections locally; merge questions into the research agenda | Preserve the explicit conjectural status of the sixth/seventh-index counts. |

The standalone introduction and reproducibility appendix can be shortened
when integrating into the larger manuscript, since it already establishes
many conventions. The article PDF should remain available as a complete
research snapshot.

## Claims to promote

| Existing label | New justification | Precise scope |
|---|---|---|
| `signed:conj:rank` | `newrank:thm:smith` | Both ranks in every odd weight, plus integer invariant factors and even-weight ranks. This is a formal matrix theorem. |
| `cm:res:d15` | `cmnorm:eq:G4d15`, `cmgenus:eq:recorded15` | The weight-four product and ratio, with the manuscript's real-part convention. |
| `cm:res:d20` | `cmnorm:eq:G4d20`, `cmgenus:eq:r420` | The weight-four product and ratio. |
| `cm:res:d23` | `cmnorm:eq:G4d23` | The weight-four full class product. |
| `cm:res:d39` | `cmnorm:eq:G4d39` | The weight-four full class product. |
| `cm:res:d47` | `cmnorm:eq:G4d47` | The weight-four full class product. |
| `cm:res:genus` | `cmgenus:eq:r439` | The discriminant -39 genus ratio, with exactly the stated class grouping. |
| `cm:res:H39`, `cm:res:H47` | `cm_norms.py` coefficient certificates | Exact class polynomials follow from interval enclosures plus CM integrality. |

The new threshold is `K_5^cl = 3`. This extends the existing small-index
results rather than contradicting their stated `n <= 4` restriction.
The small-parameter and alternating-motion theorems refine the Lerch
research questions without invalidating the fixed-index, large-derivative
asymptotic formulas.

## The two textual corrections

`text_corrections.patch` applies from the repository root. It was checked
against an isolated copy of the pinned sources with `patch -p1 --dry-run`.
For a git checkout, the corresponding review command is:

```bash
git apply --check /path/to/text_corrections.patch
```

The patch changes only:

1. **Rank-difference logic.** The two individual ranks imply the
   Gaussian-supported dimension; the dimension alone does not determine
   the two ranks. “Equivalently” becomes “Consequently.”
2. **Modified even polylogarithms.** The summary of golden ladders cannot
   identify a real-argument `P_6` combination with a nonzero zeta(6)
   multiple when the definition takes the imaginary part. The replacement
   preserves the separate status of the raw classical-polylogarithm identity.

The patch deliberately leaves promotion of the rank conjecture to the
integration of its complete proof. It does not change unrelated formulas.

## Notation and cross-references

The archive uses `Li_(a,b)(x,y) = sum_(m>n) x^m y^n/(m^a n^b)`.
The order of the two colors must be retained. The alternating Dirichlet
eta is written `eta_alt`; the CM eta is the Dedekind function.
The polynomial `mathscr R_(n,k)` in the small-parameter section is the
integer differentiation polynomial, whereas `R_(n,k)` in the Euler–Maclaurin
section is the normalized spectral polynomial. They are intentionally
distinguished.

All 144 labels in the assembled article were checked: none collided with
the pinned manuscript and none were duplicated internally. The validation
report records this check and confirms that every source reference resolves. Preserve the distinct prefixes or update every reference when
renaming labels.

The component TeX files require the standard AMS theorem environments,
`booktabs`, `graphicx`, `hyperref`, `xurl`, and `mathrsfs`. The baseline already
provides most of these; add `mathrsfs` if retaining the script-R notation.
The standalone preamble shows the complete requirements.

## Data and proof boundaries

Keep the scripts and receipts next to the integrated manuscript's existing
certified-computation material. The JSON claim ledger gives exact paths.
The two independent genus arithmetic implementations check the same six
radical identities, one with SymPy and one using only rational pairs.

The fold decimals remain a numerical diagnostic. Its existence and
nondegeneracy are proved independently. The sixth/seventh-index root counts
remain conjectures. The `S_4` mixed-relation conjecture and the higher
algebraic ladder conjectures are not promoted.

The genus formulas apply to a specified nontrivial genus character.
When the genus rank exceeds one, its two sign fibers are unions of genera.
Absolute products require an additional phase calculation before being
rewritten as raw complex products. Nonmaximal orders have an untwisted
norm formula here; their twisted genus conductor factors remain open in
this continuation.

The continuation makes no claim of arithmetic independence of the periods
and does not identify the finite formal relation module with the full space
of polylogarithmic relations. No repository push or publication is included.
