# Supplemental proposal audit at the final review cutoff

## Scope and immutable snapshots

The principal report and its source/proposal manifests remain pinned to
`1a59f50680e470fb5269bbe70c06f974c95ad930`: 26 proposal directories and 79
non-attribution Markdown/LaTeX texts. Before delivery, a further remote update was
found at `0ae2eb38ee385fa1a22fb36bb5ad65d909a259b1`. This supplement audits its two
new directories without changing the principal source snapshot or claiming a
full replay at the later revision.

All 79 previously audited text files have identical Git blobs and SHA-256 values
at the later revision. The two additions contain **20 non-license prose files:
7 LaTeX, 6 Markdown, and 7 plain-text files, totaling 236,109 bytes**. The review
read both full mathematical reports, all included sections, READMEs, migration
notes, independent reviews, exclusion inventories, and formal/validation scope
notes. The exact 20-file list, sizes, Git blob identifiers and SHA-256 hashes are
in `supplemental_update_manifest.json`.

Thus the later revision has 28 proposal directories. The two audit stages cover
the original 79 texts plus these 20 additional texts. The difference in suffix
policy is explicit: the original count refers to Markdown/LaTeX, while this
supplement also includes seven substantive `.txt` files in the Frobenius bundle.
The added upstream license and attribution notices are excluded from the novelty
corpus. PDFs, executable code, and structured evidence files were not counted as
additional prose reports or independently validated by this supplement.

This later commit is the cutoff for this delivery. The claim is relative to the
audited repository corpus, including the previously reviewed but subsequently
removed `robust_theta_labels` proposal. It is not a claim of global literature
priority or of coverage of future repository changes.

## Added mechanisms that are now exclusions

### 1. Finite Frobenius certificates for the local theta exponent

Directory:
[`grh_frobenius_jet_simplification`](https://github.com/VladimirReshetnikov/ProveIt/tree/0ae2eb38ee385fa1a22fb36bb5ad65d909a259b1/Analysis/GeneralizedRiemannHypothesis/docs/proposals/grh_frobenius_jet_simplification).

The report retains the exact theta-product factorization with its raw integral
exponent and replaces the complete double-indexed coupling normal form by two
consumer contracts. Finite null-moment vanishing proves local divisibility;
selected first-gradient coefficients prove inert-prime sharpness. The finite
Artin–Schreier resolvent and the weighted Frobenius pairing identity replace an
infinite prime-power support classification. The gradient certificate retains
unit leading coefficients, while the divisibility certificate works over the
possibly nonreduced quotient by the source's distinguished small element.

Its source targets are `SeriesCongruences`, `FormalGroup/Exponent`,
`Divisibility/NormalForm`, `FormalGroup/ThetaProducts`, and their derivative
consumers. Its migration and independent-review notes retain the formal-group
input, the exact exponential factorization, the ramified degree-two moment,
natural-number weights, and the one-extra-degree derivative precision.

**Effect on the present proposal:** this is a separate local power-series
interface. It does not identify the first-path finite gauge group, calculate
its stabilizer, normalize `firstPathDatum`, obtain initial root budget one, or
collapse the first-column period scalar. Its use of a weaker sufficient
certificate is conceptually analogous to a general proof-design principle;
that principle is not claimed as novel here. The coefficient arithmetic
contract proposed in the principal report concerns finite auxiliary-path
coefficients and a terminal class sum, not the formal theta exponent or its
gradient/divisibility certificates. Both changes can be implemented.

### 2. Direct scalar-height certificates and one-vector branching norms

Directory:
[`grh_simplification`](https://github.com/VladimirReshetnikov/ProveIt/tree/0ae2eb38ee385fa1a22fb36bb5ad65d909a259b1/Analysis/GeneralizedRiemannHypothesis/docs/proposals/grh_simplification).

The first mechanism replaces exact exchange-scalar modulus metadata with
guarded, additive height budgets for the normalized squared modulus of the
actual complex period scalar. It proves exact positive-power descent for the
source's common-multiplier `HeightLe`, retains a mixed ambient Gram identity,
and propagates determinants directly through the triangle. The explicit
boundary Euler-factor cancellation, common twist family, zero-target branch,
and nonvanishing obligations remain. The report credits the compact edition's
earlier squared-cost and determinant-first architecture.

Its second mechanism shortens the branching norm argument using the Gram
adjoint and Schur's lemma, calibrating the resulting scalar at one highest
weight vector. It credits the compact source's Cartan-product calibration and
also develops an optional fixed-unit-tensor/signed-coordinate calibration.
This replaces the readable branching proof's general extended-tensor route.

**Effect on the present proposal:** neither mechanism evaluates the initial
finite gauge average. The scalar-height certificate belongs to the period
comparison scalar `c(θ)`, whereas the principal report's arithmetic certificate
belongs to each finite coefficient `F_θ(S)`. They have different domains,
mathematical content, and downstream consumers. The new report explicitly
retains Fourier/coefficient integrality, exact period identities, and the
auxiliary spanning/size arguments.

The present normalization preserves the actual period scalar and its existing
height certificate. References in the principal report to the old
`HasAbsUpToNormPower` API should be read as compatibility statements for the
pinned source; after this added proposal is implemented, use its direct height
certificate instead. The initial normalization introduces only a fixed scalar,
which cancels in normalized twist ratios. No new scalar-cost calculus,
reverse-power height theorem, determinant-first triangle, or highest-vector
branching reduction is claimed here.

## Final nonduplication conclusion

The specific remaining contribution is the exact source-level identity

\[
\Psi^0_\vartheta
 =d_0\left(\prod_{i=1}^{m-1}h_i\right)\Omega_\vartheta,
\qquad
\Omega_\vartheta(S)\in\{0\}\cup\mu_\infty,
\]

with a twist-independent product of all residual false congruence-kernel
cardinalities, and the compatible first-column scalar `d_0/h_0`.

The already proposed single redundant true-slot deletion is assumed available;
the new step evaluates **every remaining transporter fibre**. The underlying
finite character-sum lemma is standard. The source-specific stabilizer,
two-modulus endpoint coupling, uniform multiplicity, and arithmetic-safe
normalization are the content being proposed. None of the 20 added prose files
contains this result or proposes it as a future direction.

The optional replacement of the auxiliary root-multiset invariant by universal
coefficient integrality plus a complex-automorphism bound only at the trivial
twist, followed by one exact joint terminal class expansion, also remains
additional. It should be presented as a separate source-interface change, with
its terminal expansion and Lean adapters still to be integrated. The newer
reports do not remove those obligations.

The earlier exclusions remain: deterministic sweeps, diagonal-only Fourier
costs, active-frontier data, sharper endpoint counts, redundant true-slot
deletion, local orbital matching, bottom-of-tower Reynolds averaging, and all
other mechanisms in the 26-directory inventory. No discarded sweep/frontier
idea has been revived under a new name.

## Source changes and verification boundary

The later update changes eight Lean files outside `AuxiliaryForms`, plus two
source indexes. Every file in `New/Determinant/AuxiliaryForms` is unchanged.
The eight modified Lean files are:

- `Lib/Adelic/AutomorphicForms/PAdicGauge.lean`
- `Lib/GLn/SchurModule/SchurOrthogonality.lean`
- `Lib/Weil/MixedModel/SchwartzBruhat.lean`
- `New/Congruences/FirstOrder/RibetMethod.lean`
- `New/OneLift/ComparisonOperator/GluingMaps.lean`
- `New/OneLift/FalseLifts/BottomOfTower.lean`
- `New/OneLift/LiftVolumeHeight.lean`
- `New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean`

In particular, `PAdicGauge` is a supporting source cited in the principal
manifest and did change. This supplement does not assert that all 27 principal
source files remain unchanged or that their later implementations have been
reverified. The mathematical/report claims continue to use the immutable
`1a59...` snapshot; this later audit updates the novelty exclusion boundary.

The supplemental manifest records the actual source path changes and checks
the old proposal blobs. Reading reports and hashing them establishes the review
corpus and its integrity, not the correctness of their mathematics, their claimed
Lean builds, the entire RH/Dirichlet-GRH development, or measured net savings.
