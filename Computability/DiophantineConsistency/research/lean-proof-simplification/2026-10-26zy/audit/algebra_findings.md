# Algebra/arithmetic review: one retained narrow proposal

Pin: `3299f4aa4c9ae38b0f5a1c00a1f0d23f6cbdb114`.

## Retain: prove the Pell factor-two bound from the single lifting row

Target: `Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativePellBootstrap.lean`, declaration `source_Y_ge_two`, lines 95–115 at this pin. Its direct callers include `source_rank_half_lt` (lines 119–138) and `source_base_separation` (lines 348–363).

The existing proof uses both source rows 0 and 1. It sets q=1+Jβ, proves q≥2, uses row0 to obtain L=q²−1≥3, and obtains N=q(1+L)≥8, only to conclude N*s≥2. All source coordinates are already positive. Thus L≥1 and s≥1 are already hypotheses; row1 gives N=q(1+L). With q≥1, this directly yields N≥2 and hence N*s≥2. Neither L=q²−1 nor N=q³ is required.

The strongest minimal statement needs no beta sign condition at all. Let β be any integer and J,L,N,s be natural numbers. Assume L,N,s>0 and the literal row1 equation

  -1 - L + N - β*J - β*J*L = 0.

It factors as N=(1+βJ)(1+L). Because N>0 and 1+L>0, the integer q=1+βJ is positive, hence at least 1. Since L≥1, N≥2, so N*s≥2. This can be viewed as a proper positive divisor certificate. J need not be positive.

A smaller compatibility proof retains the old `hβ : 0 < ports 0` premise, uses only its nonnegative consequence and obtains N≥2 directly by nonlinear arithmetic from row1. It does not introduce a helper, extra import, altered executable definition, or changed public statement.

## Why this remains additional after prior work

Packet **b**, `report.tex` lines 617–641, explicitly proposes decoding source-register identities once and names `source_Y_ge_two` among its clients. That earlier proposal is assumed applied. Therefore the current raw-source deletion of repeated extraction/casts MUST NOT be credited as novel.

The remaining new observation is the unnecessary strength of the old argument: with the old semantic interface already present, the client still need not consume L=q²−1, N=q³, q≥2, or N≥8. It only consumes the multiplicative lifting identity and positivity. The dependency on source row0 disappears, and the stronger theorem no longer requires a sign hypothesis on beta. The novelty auditor conditionally accepted precisely this narrow distinction.

This is a small local improvement, not a new general algebraic framework. Net source savings after fully applying packet b have not been measured. The supplied patch's eight-line reduction is relative to the actual pinned source only, and must not be added to savings already promised by packet b.

## Artifacts and validation

`lean/MinimalPellBootstrap.lean` imports narrow Mathlib tactic modules and proves ten named results:

- `semantic_lower`: the short client using N=q(1+L), q≥1, L>0, s>0;
- `raw_lower`: raw literal row1 with β≥0;
- `raw_lower_no_beta`: raw row1 using positive L,N,s and no beta restriction;
- `compatible_source_Y_ge_two`: exact literal source-row arithmetic retaining the old beta hypothesis;
- `stronger_source_Y_ge_two`: pointwise source theorem using only three coordinate positivities and row1;
- `beta_pos_from_two_rows`: scalar recovery of beta positivity from rows0/1 and positive L,N;
- `source_beta_pos`: pointwise source wrapper for that recovery;
- `PinnedSource.source_Y_ge_two`: the compatibility proof bound to the byte-exact maintained source table;
- `PinnedSource.source_beta_pos`: beta recovery bound to that exact table;
- `PinnedSource.source_Y_ge_two_without_beta`: the exact-table bound with no external beta premise.

Lean 4.32.0 checked the complete prototype file with exit status 0. The final log `evidence/algebra/MinimalPellBootstrap.check.log` prints ten axiom reports (including beta recovery and the exact-table wrappers): each contains only `propext`, `Classical.choice`, and `Quot.sound`; none contains `sorryAx` or new user axioms. The compiler used existing read-only Mathlib 4.32 package oleans and no ProveIt oleans.

`patches/B1-source-Y-row-one.patch` is an exact unified diff against the pinned production source. It preserves the old declaration header, executable definitions, and imports; the declaration spans 21 old physical lines and 13 candidate physical lines. The patch has NOT been checked by recompiling the full production module/import closure. A byte-exact extraction of the maintained `SplitCertificate59.sourceRows` definition was added to the checked prototype, and `PinnedSource.source_Y_ge_two` checks the exact candidate body against it. The source table copy was verified byte-for-byte; its region hash is in `source_rows_binding.json`. Thus the finite-table binding as well as the arithmetic is kernel checked, while import-graph integration remains unverified. Production adoption still requires rebuilding `NativePellBootstrap` and its clients.

`evidence/algebra/source_y_metrics.json` records this distinction. No repository file was modified.

## Optional propagation, without counting another idea

A stronger no-beta source theorem can feed `source_rank_half_lt` and `source_base_separation`, eliminating their beta premise where its sole use is `source_Y_ge_two`. This is a consequence of the same proposal, not an independent contribution. Keep original public declarations as compatibility wrappers if downstream callers depend on their signatures; count the wrapper overhead. Completeness and port-calibration APIs that use beta positivity independently must retain that condition. Do not broadly remove `PortBox.beta_pos`.

## Rejected arithmetic directions

1. Congruence modulo sign for `NativePellStepDown` is explicitly in packets j/m and subsequent ledgers.
2. Elementary row operations or a polynomial/invertible matrix certificate for `NativeArithmetic52.eq_lift_of_zero` and `SplitCertificate59.transformed_zero_iff` is already packet c, report 774–808, including the full invertible combination extension; reject.
3. Pell recurrence monotonicity, error factors, fixed index-six anchors, exact rational-root descent, and small-ordinate fundamental-unit arguments are explicit prior work; reject.
4. Coefficient l1 envelopes, compositional linear bounds, sparse list semantics, polynomial identities before interpretation, and semiring transport are explicit prior work; reject.
5. Fixed controller residues, full-modulus certificates, prime-order tests, LTE/exponent spectra, and whole-polynomial Gamma nonvanishing are in late z packets; reject.
6. Per-cell carry folds, reset locality, block complements, point-update weighted sums, and scalar rank-affine changes are prior work; reject.

No second algebra proposal passed the strict non-repetition standard with enough benefit to recommend. Offering a new spelling of one of these would weaken the report.

## Further consequence: recover beta positivity from a source zero

The checked `beta_pos_from_two_rows` and `PinnedSource.source_beta_pos` make the beta sign an output. For natural J,L,N with L,N>0, source rows0/1 give

  L=q²−1,  N=q(1+L),  q=1+βJ.

The second equation implies q>0; because q is an integer and L>0, the first implies q≥2. Therefore βJ=q−1>0; since J is a nonnegative natural, β>0. The theorem does not need a separately supplied J>0 premise. These are local polynomial equations and order facts, so no consistency endpoint is used to prove the guard.

This recovery permits a source-only version of existing bootstrap theorems. The original compatibility statements can remain. Do not claim a new line reduction merely for adding wrappers, and do not remove external beta guards from functions that operate on arbitrary assignments rather than known positive source zeros.

The novelty auditor accepted this narrowly as recovering an input port's sign from actual solution equations; packet b only decodes the identities, and packet f's stronger `PortBounds.beta_min` is an external assumption. The local factor-two bound and sign recovery belong to one related proposal family.

The exact 22-row source definition copied into the prototype has SHA-256 `bb4b3bba67a6c924be4659789ddad7e87fa7cb050f1343dc939e6e74a523deca` and 1774 UTF-8 bytes. It is exactly the maintained declaration, not a separately simplified replacement; only its namespace differs. Focused table extraction uses no project `.olean` files. All ten theorem checks completed with exit status zero under Lean 4.32.0; none introduces new axioms or `sorry`.
