# Integration notes

Prepared 12 October 2026 for ProveIt revision
`c4036d60715916ae72dd18983782fdb182840b86`.

This package is a proposed incoming research article. It does not modify the
repository or replace any existing theorem status automatically.

## Recommended integration units

| New source | Destination or predecessor | Status change |
|---|---|---|
| `sections/01_gamma.tex` | Ordered Boundary Identities, `sections/08_gamma_basis.tex`, after `gb:normalization` | Evaluate every `K_m`; mark research question 2 resolved |
| `sections/02_gaussian.tex` | New section following the Gamma moment determinant | Add paired deformations, exact finite trigamma moments, and their proved Gaussian limit |
| `sections/03_colored.tex` | Balanced Stieltjes Moments, after scalar Mellin/ordinary moment developments | Resolve research question 4 in the displayed homogeneous ansatz; retain the open-interval uniqueness hypothesis |
| `sections/04_clusters.tex` | Lattice Contacts, `sections/07_spectral_faces.tex`, after `sfj:thm:gamma-polylog` | Resolve the two-distinct-mass-value sector and record the supplied depth bound |
| `sections/05_parity.tex` | Manuscript `chapters/04-depth.tex`, Family 2 worked example | Add an exact finite proof/certificate; do not change `S_6` or revised `S_8` status |
| `sections/06_audit_research.tex` | Research and audit ledger | Update only the specifically resolved questions and preserve the remaining scopes |

All newly introduced theorem/equation labels use `gn:`, `col:`, `tc:`, or
`par:` prefixes, except section-level article labels. Reconcile macros such as
`\dd`, `\Li`, `\src`, and `\pin` with the manuscript preamble during integration.
The bibliography is plain LaTeX and can be merged by key.

## Results that must remain distinguished

1. Gustafson's multivariable Barnes integral is classical. The new step is its
   application to the incoming normalization and the proved parameter/moment
   consequences. Do not label the classical integral as newly discovered.
2. The initial Gamma-basis determinant is evaluated. This does not prove
   nonvanishing of all later harmonic-tail determinants.
3. The positive Gamma ensemble has exactly Gaussian moments through degree
   `n+1`. The theorem does not claim a Gaussian distribution at finite `n`, or
   maximality of that matching range.
4. Colored uniqueness holds for coefficients independent of the shift and a
   decay condition on a nonempty open shift interval. The supplied fixed-shift
   counterexample shows why this scope matters.
5. Ordinary color-one constant terms depend on whether the centering factor
   `exp(-a lambda)` is included. The conversion polynomial is explicit.
6. The two-cluster dictionary is finite per spectral term. It does not remove
   the outer lattice sum, prove minimal depth, or cover three distinct masses.
7. `S_6`, revised `S_8`, and unrestricted unequal-tail reconstruction remain
   conjectural. The small weight-three certificate is not a higher-weight proof.

## Source paths

The three principal incoming predecessor archives are:

- `docs/incoming/ProveIt_Ordered_Boundary_Identities_2026-10-11.zip`
- `docs/incoming/ProveIt_Balanced_Stieltjes_Moments_2026-10-11.zip`
- `docs/incoming/ProveIt_Lattice_Contacts_and_Mixed_Zeta_Identities_2026-10-11.zip`

The manifest in `evidence/source_manifest.json` records all eleven incoming
archive hashes at the inspected revision. The article identifies the exact
inner theorem labels used; wrapper directory names in the archives are retained
in that manifest where relevant.

## Optional editorial patch

`remove_duplicate_readme_paragraph.patch` removes a consecutive duplicate
paragraph in `Analysis/Polylogarithms/docs/manuscript/README.md`. The patch is
against the pinned revision. Check the current file before applying it if the
repository has moved on. The paragraph's mathematical statements are retained
once; the patch makes no mathematical assertion.

## Review standard

The article supplies analytic proofs and exact algebraic certificates, together
with independent high-precision diagnostics. Numerical records are not certified
interval enclosures, and the package is not a proof-assistant formalization or
an independently refereed publication. Historical priority has not been proved.
