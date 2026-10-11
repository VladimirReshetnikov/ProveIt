# Integration guide

## Baseline and intended placement

This is a continuation of the unified polylogarithm manuscript and the five current incoming polylogarithm reports at commit `445f754610e1377939235794de84ed9075fc09f5`. A suitable standalone destination is `Analysis/Polylogarithms/docs/reports/exact-identities-2026-10-10/`; placement is left to the repository's intake process.

The complete article compiles independently. For a chapter merge, preserve the proof and convention sections before importing isolated formulas. Every internal TeX label has the prefix `xid:` to avoid collision with existing manuscript labels. Citation keys may be merged with the host bibliography after matching the actual references.

## Section map

| Source file | Natural host topic | Essential retained convention |
|---|---|---|
| `sections/preliminaries.tex` | Stieltjes/Hurwitz foundations | `gamma_n` uses the standard alternating Laurent sign; zeta superscripts are order derivatives, gamma/psi superscripts are argument derivatives. |
| `sections/collision.tex` | Two-frequency Stieltjes correlations | Fixed ambient right cutoffs; the complete pole numerators; no product of colliding distributions. |
| `sections/nonlinear.tex` | Dilation and coordinate laws | Scalar distribution pullback includes its Jacobian; the unit-tangent thresholds require `f'(0)=1`. |
| `sections/triple_dilation.tex` | Triple correlations | Pairwise disjoint rational grids; shift derivatives stay inside one separated chamber. |
| `sections/fully_shifted_height_one.tex` | Generalized harmonic zeta functions | Every denominator is shifted, but only the outer exponent varies; strict versus inclusive harmonic sums are distinct. |
| `sections/weighted_arctangent.tex` | Chapter 03 weighted bilinear integrals | Real arctangent branches; branch prescriptions for the more general ordinary primitive. |
| `sections/audit_research.tex` | Status ledger and next questions | Numerical checks are not proofs; short S6/current S8 remain unresolved. |

## Precise status changes

The Mellin–Dilation report's colliding-grid question is answered for all positive integer dilations and all nonnegative indices by the master kernel, its zero-order supplement, and the convergent collision expansion. Its separated theorem stays valid as written; replace the future-work question with a cross-reference to this result rather than deleting its separation hypothesis.

The nonlinear-coordinate question is answered for orientation-preserving analytic local diffeomorphisms, including finite-jet dependence, composition, and exact endpoint primitive constants. The correction at nonunit tangent generally survives at arbitrarily high Stieltjes index; the sharp finite threshold is specifically a unit-tangent statement.

The unequal triple-frequency question is answered when all three grids are pairwise disjoint, including every Stieltjes and argument coefficient. Colliding triples remain open.

The fully shifted height-one family extends the existing outer-only-shift family. Its entire correction cannot be discarded: doing so already gives the wrong depth-zero value at `s=0`. The new all-depth statements must retain the attribution to the existing depth-one harmonic Hurwitz-zeta literature.

The weighted arctangent paragraph after `cleo:eq:lintanh` can now cite the exact real addition formula and its complete primitive. The original observation that the unweighted single-product reduction fails remains correct; the new article proves that restricted obstruction exactly while supplying a different two-term formula.

## Conjectures whose status must stay unchanged

- `gauss:eq:S4-closed`: already proved in `04-S4-proof.tex`.
- `cycloquot:conj:S6`: unresolved.
- `s8new:conj:S8`: unresolved; different from the previously rejected vector.
- `research:prop:S8-rejected`: the earlier rejection remains in force.
- Higher golden `Li_6`–`Li_9` numerical vectors: no proof supplied here.

The current article does not repeat already established incomplete-beta generators or the latest two-shift reflection as new results. The novel-relative-to-source claims are listed individually in `claim_ledger.json`. Historical priority is not asserted without a fuller literature comparison.

## Narrow correction patch

`canonical_corrections.patch` changes only the real logarithm in `cleo:eq:lintanh` and the unsupported description of the unweighted `(1,1)` diagonal. `CORRECTIONS.md` documents both changes and credits the earlier report that first flagged them. The patch was checked and applied only to a temporary copy of the pinned file. Review it against the current repository before applying it if the host has advanced.

## Reproducibility and formal status

The article has analytic proofs and executable exact/numerical audits. It contains no Lean files and does not confer formal status on the corresponding ProveIt statements. The seven mathematical scripts can be run with `python code/run_all.py`. The complete source and figures are self-contained; no external image assets or downloaded source papers are needed.
