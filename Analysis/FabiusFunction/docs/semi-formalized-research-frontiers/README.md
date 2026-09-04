# Semi-formalized Fabius research frontiers

This directory is the boundary layer between the prose mathematics of the
Fabius function and Rvachev's up-function and the Lean corpus that verifies
it.  It was originally a pure quarantine: everything here lacked an exact,
audited Lean theorem covering its full hypotheses and conclusions.  That is
no longer the shape of the collection.  Much of it has since been
formalized, in some cases more generally than stated here, and each volume
carries a crosswalk naming the declarations that discharge its claims.

So the contents are *mixed*, and the point of the directory is now to keep
the two sides in correspondence rather than to hold one side apart: every
claim should either name the Lean theorem that proves it or say precisely
what is still missing.  `scripts/audit_all.sh` enforces the mechanical half of that:
facade reachability, exact crosswalk names, declaration-name uniqueness, and
the names advertised by module docstrings.  `scripts/audit_stale_claims.py` reports the
half that needs reading.

The canonical frontier artifacts are:

- [`semi-formalized-research-frontiers.tex`](semi-formalized-research-frontiers.tex)
- [`semi-formalized-research-frontiers.pdf`](semi-formalized-research-frontiers.pdf)

> **Accepted final-source receipt.** The current source has 17,983 lines and
> 806,798 bytes, with SHA-256
> `a1cb1c0db2784116ca1f1d6fd1ce7e8b29afc52c64c93e7001bbffb91f775039`.
> Three passes produced 252/260/260 pages.  The accepted 260-page,
> 1,877,420-byte A4 PDF has SHA-256
> `78c19b361da06836c20c62fa5bd50131eb8fa47d3e89d37a7f089a51568953b3`;
> its final 2,990-line, 101,866-byte log has SHA-256
> `4854a89ba1a3bb41248b9428cfed572f6ed593125b5a8fb43d5625d8d392dc0f`.
> All documented log, page, font, Type-3, extraction, and visual gates passed;
> the page-176 running-head collision was repaired before acceptance.
>
> **Historical receipts.** At commit `581bf`, the source had 17,947 lines and
> 804,625 bytes, with SHA-256
> `ac6b28fb8a98d97ed4b7a0fe7a5ba2cdfab852fb6de1ee2ecfda4aed75804371`.
> Its matching 260-page, 1,875,190-byte A4 PDF has SHA-256
> `fee3b5af21b01b16c41cf8291ba0508d1e6c613bfd098cdef457cde44ea693c2`.
> The later 17,982-line, 806,760-byte source-only pin, SHA-256
> `6edfc099f275f74d6e3ae5b74e60a2fcf4aeca313089967dafbae4b2585bf2d4`,
> records the post-merge state before the final running-head repair and is now
> superseded historical evidence.
> The preceding 257-page, 2,438,299-byte A4 PDF, SHA-256
> `3766761aac90247061f5c955dc84a0feb8567454e10839f1508b9431797ee980`,
> remains a historical receipt for the source before the later q-Pochhammer
> overlay and expanded ledger.

On the local publication line, Gaussian revision `71c908e` was the
902/11,443 checkpoint, completed Lambert--Bernoulli revision `217a6b9` was
903/11,448, and the five fixed-column declarations brought commit `581bf` to
903/11,453. At `581bf`, the primary exposition, Lean walkthrough, Lambert
Guide, consolidated q-series synthesis, and canonical frontier received exact
final-source renders: respectively 187, 150, 70, 391, and 260 A4 pages. Their
exact source and PDF receipts remain recorded here, in the root README, and in
the documentation audit as historical evidence. The parallel upstream-only
moment-polynomial revision `3b6396` was 904/11,457; merging it with `581bf`
gives the 904/11,462 union and changes those five TeX sources as well as the
independently published standalone geometric-q root. All six final-source
renders are now accepted with exact source, PDF, and final-log receipts; their
documented log, A4 page, font, Type-3, extraction, and visual gates passed.

The superconvergence overlay initially postdated every then-retained frontier
PDF. `RvachevSuperconvergentSynthesis.lean` contributes one
definition and eight theorems for arbitrary nonzero natural meshes: it
packages the parity-selected phases, exactness through degree `v₂(M)+1`,
physical-coordinate quadrature, deconvolved-polynomial synthesis, and the
explicit Rvachev--Appell specialization. In the canonical inverse synthesis
this promotes exactly `is:p3:cor:forced-superconvergence` and
`is:p3:thm:Appell-lattice-reproduction`, bringing its 194 immutable rows to
49 Lean-proved / 96 human-proved / 10 conjectural / 15 open / 24
nonassertoric. At that superconvergence checkpoint the documentation census
was 671 modules and 8,858 public declarations; no PDF was rebuilt for that
source-only update. The overlay is present in the exact `581bf` primary,
walkthrough, and canonical-frontier receipts, which are now historical after
`3b6396`. The accepted current primary, walkthrough, and canonical-frontier
renders also include it; the unrelated inverse and comb artifacts remain
historical with their existing statuses unchanged.

The later Lambert branch-coordinate overlay formalizes the exact
pairing theorem, its symmetric corollary, the compact Bernoulli-series identity,
and the complex Bernoulli generating function with its standard removable
value and exact convergence radius from `Lambert_W_Guide/`.
`LambertWBranchPairing.lean` has 0 definitions + 7 theorems,
`LambertWGapBijection.lean` has 4 definitions + 16 theorems, and
`LambertWBranchSymmetry.lean` has 0 definitions + 9 theorems. For
`x in (-exp(-1), 0)` and `delta = W_0(x) - W_{-1}(x) > 0`, they prove the two
exact branch formulas, the explicit inverse and gap bijection, the equivalent
`t = exp(delta) > 1` coordinate, the ratio/sum/product identities, and the
strict bounds `W_0 + W_{-1} < -2` and `0 < W_0 W_{-1} < 1`. The proof divides
the two equations `W_j exp(W_j) = x`, then uses branch-range uniqueness for
the converse; `sinh(y) > y` and `y coth(y) > 1` give the strict bounds.
The interval is deliberately open: at the branch point the rational formulas
have zero denominator and their limiting sum/product are `-2` and `1`, while
zero is the singular classical lower endpoint.

The companion `LambertWBranchGapBernoulli.lean` has the exhaustive surface
0 definitions + 5 theorems. Alongside the real open-disk absolute-summability
theorem, `summable_bernoulli_mul_pow_div_factorial_iff` proves for complex `z`
that the Bernoulli exponential generating series is summable exactly when
`‖z‖ < 2*pi`; in particular, it diverges on `‖z‖ = 2*pi` and throughout the
exterior. The new theorem
`hasSum_bernoulli_mul_pow_div_factorial_complex_iff` gives the complex value
as `(complexExpm1Div z)⁻¹` exactly on that disk. This target is `1` at `z = 0`
and rewrites to `z / (exp z - 1)` when `z != 0`; it does not identify the
series with Lean's literal totalized quotient, which is `0` at the origin.
The other theorems give the all-index real quotient value away from zero and
the two paired branch sums when `x in (-exp(-1), 0)` and the positive branch
gap is below `2*pi`. Thus `eq:pair-Bernoulli-general` is Exact, and
`eq:bernoulli-gen` is wholly Exact under the explicit standard
removable-origin convention. The Guide's nearest-nonzero-zero explanation is
not the formal proof route. With the three finite branch-coordinate modules,
the four-module union is 4 definitions + 37 theorems = 41 declarations.
Higher or convergent Puiseux/logarithmic
expansions remain open. Gaussian checkpoint `71c908e` contained 902 modules
and 11,443 public declarations. The initial four-theorem Bernoulli leaf gave
the exact-radius checkpoint 903/11,447; the value-completion theorem brought
completed Lambert checkpoint `217a6b9` to 903/11,448. The five fixed-column
q-binomial declarations then brought local checkpoint `581bf` to 903/11,453.
The exact `581bf` primary,
walkthrough, Lambert-Guide, and canonical-frontier PDFs include that overlay;
the q-series PDF is the exact receipt for its own pre-upstream source. Those
five and the older standalone geometric-q PDF remain historical receipts. The
accepted current renders of all six roots include the post-merge union.

The parallel upstream addition is
`FabiusFunction.GeometricUniformMomentPolynomial`, with one definition and
eight theorems. It defines the recursive rational polynomial family and proves
its base case, residual-product recurrence, triangular degree bound,
reciprocal-factorial value at zero, and the explicit cases `P1` through `P4`.
Together with the zero theorem this is the complete displayed `P0`--`P4`
algebraic surface. It does not identify the recursive family with the
normalized analytic Taylor or moment coefficients, and it does not prove the
leading-coefficient formula or the resulting strict odd-degree drop. Thus
`p7:thm:Pn` remains **Partial**, with only its algebraic recurrence, degree
bound, zero value, and small-case clauses supplied. Based on completed Lambert
checkpoint `217a6b9`, this one-module/nine-declaration increment produced
upstream-only checkpoint `3b6396` at 904/11,457; its merge with the independent
five fixed-column declarations in `581bf` brings the live documentation census
to 904 modules and 11,462 public declarations. It was not rendered by any of
the five retained pre-upstream PDFs; it is included in the accepted current
renders of all six roots.

The preceding declaration addition is
`FabiusFunction.GeometricRichardsonGenerating`, with three definitions and
seven theorems. Its
`Fabius.geometricLagrangeRichardson_generating` theorem is the exact formal
counterpart of canonical comb label `gq:thm:richardson-generating`; the module
also supplies the report-facing analytic companion
`Fabius.hasSum_geometricLagrangeRichardson_mul_pow` under strict nome
contraction and absolute summability. The exact `581bf` primary, walkthrough,
and canonical-frontier receipts include this crosswalk, but are historical
after merging parallel revision `3b6396`. The accepted current primary,
walkthrough, and canonical-frontier renders preserve the crosswalk. The
retained comb-synthesis PDF still predates it and remains a historical artifact.

The next declaration addition leaves the module count unchanged and adds
three theorems to `FabiusFunction.GaussianBinomialCumulants`: the explicit
second derivative at one
`Fabius.eval_one_derivative_derivative_gaussianBinomial_X`, the division-free
raw second moment `Fabius.twelve_mul_secondMoment_gaussianBinomial_eval_one`,
and the division-free variance numerator
`Fabius.twelve_mul_varianceNumerator_gaussianBinomial_eval_one`. The first is a
characteristic-zero field identity on `k ≤ n`; the cleared identities are total
over every commutative semiring, including the above-row zero case. Their
probability language is the normalized-generating-polynomial interpretation of
algebraic identities, not a new probability-space construction.

The 1 September 2026 q-Pochhammer overlay initially postdated the retained
PDFs and is included in the exact `581bf` q-series, primary, walkthrough, and
canonical-frontier receipts. Those receipts are now historical after
`3b6396`; the accepted current renders of those four roots also include the
overlay. The new
`QPochhammerEntire.lean` leaf has zero definitions
and five theorems: for a fixed complex nome with norm less than one it proves
local uniform convergence of the infinite product, differentiability in the
symbol, the division-free factor-zero criterion, the reciprocal-power zero
lattice when the nome is nonzero, and analytic order one at every zero.  This
promotes only `thm:poch-entire` in the consolidated q-series monograph.  The
same current source also crosswalks the generic infinite/dissection API and
the later Euler, q-binomial, Jacobi, quantum-binomial, Rogers--Szegő,
cyclotomic-divisibility, q-Catalan, primitive-root-block, q-Lucas, Jackson
q-beta, geometric Newton-interpolation, integer/complex upper Gaussian, and
q-Pfaff--Saalschütz, and noncommutative q-multinomial tranches.
`QBinomialTheoremInfinite.lean` now has one definition and twenty-seven
theorems.  Its five newest declarations are
`norm_finiteQPochhammerIn_pow_sub_one_le_exp`,
`isBigO_finiteQPochhammerIn_pow_sub_one`,
`tendsto_gaussianBinomial_add_atTop`,
`isBigO_gaussianBinomial_sub_inv`, and
`isBigO_gaussianBinomial_add_sub_inv`.  They add an explicit finite-product
error bound, its geometric rate, arbitrary fixed upper-index shifts in the
Gaussian limit, and unshifted/shifted geometric error rates.  The manuscript's
fixed-column limit/rate claim is therefore Exact.  Lean states the errors in
additive `IsBigO` form as `O(q^(n-k+1))` and, after shifting by `k`,
`O(q^(n+1))`; multiplying by the fixed nonzero denominator `(q;q)_k` gives
the equivalent relative-error form used in the manuscript.  Its
282-result forward status totals are now 167 Exact / 90 Partial / 17 None / 8
N/A interface rows: the fixed-column row is Exact, while the newest
moment-polynomial row has moved from None to Partial. The outer spectral
product now has an exact
locally-uniform/normal-convergence theorem; the compound centered/MGF and
exterior reciprocal/pole layers remain partial.

The final terminating-basic-hypergeometric inventory is
`TwoPhiOneReversal.lean` (2 definitions + 12 theorems) and
`QChuVandermonde.lean` (10 theorems). The two q-Chu evaluations and the
terminating reversal lemma are exact for the actual `twoPhiOne` tsum. The
claim that reversal alone proves the second evaluation on its full displayed
domain remains partial: the compiled by-reversal theorem retains `C ≠ 0` and
`(A;q)_n ≠ 0`, while the unrestricted theorem uses finite q-Cauchy directly;
no rational-continuation or cleared commutative-ring extension is claimed.

Immediately before the Gaussian second-moment edit, the monograph source had
16,359 lines and 812,257 bytes, with SHA-256
`e90f46955d9a9792ce469d29ceaa3aa538874eb1e94cf4c2dd7e50dbaf63b10e`.
The formerly retained 389-page A4 PDF (3,254,138 bytes; SHA-256
`b8add607c85ee35be98dabf36879e1d45fb093c6b453e93679c80295fae715bc`)
was synchronized to the preceding 16,339-line, 810,779-byte source checkpoint
(SHA-256 `14c444feb14c435bc300becd9c8cd2765c1e96f608dd79da462becc41b28ed22`).
The 16,359-line checkpoint already included the merged q-Chu/reversal union.
The Gaussian-moment and fixed-column theorem tranches postdated that historical
receipt. The exact pre-upstream q-series receipt frozen at `581bf` is a
391-page, 2,464,122-byte A4 PDF with SHA-256
`c0a00720685f40e0684b4858e7ce18ce134701529898fd4574d09b6c090e0e91`.
It matched the 16,433-line, 815,194-byte master with SHA-256
`f2aae6ddc3d7a399f9ed47806a0abe6458cbcab37bf2aac9f55ad3913b5a0e2d`.
After merging parallel revision `3b6396`, the live master has 16,448 lines and 816,185 bytes, with
SHA-256
`a463abef7bb3c70e12a568a46fc192aac88a8ce240f8f781fff2b018a4aa086d`;
the full 26,114-line, 1,168,039-byte source graph has aggregate SHA-256
`d4c5b84cc07f6abb99279c5bba4fdf7404326426cbe81f4b33b72ba01e62739c`.
Three passes at 383/391/391 pages, with `makeindex` after each pass (164
accepted, 0 rejected, 0 warnings), produced the accepted 391-page,
2,464,712-byte A4 PDF with SHA-256
`a52eb90dec7b874cc29dea891a107b9eb2d55e6727eb8bd8943d0aab609c58a6`.
The final 1,231-line, 44,343-byte log has SHA-256
`fb74b0c4cbd75d9022c78c1df5c1d567120bd67728d5b418697ddc5a2aa8f450`;
all documented gates passed. The 391-page `581bf` PDF above remains a
historical receipt rather than the current artifact.

The current finite-moment/Legendre/Gaunt crosswalk covers eleven modules with
20 public definitions and 109 public theorems, 129 declarations in all. The
new leaves are `LegendreGauntClosedForm.lean` (2 definitions, 25 theorems) and
`FabiusLegendreGauntClosedForm.lean` (0 definitions, 3 theorems). They define
the parity-and-weak-triangle support and the total rational square of the
integer-index zero-row Wigner datum, prove the central-binomial and factorial
forms, identify both rational and real Legendre Gaunt coefficients with twice
that square, characterize their exact zero/positive support, and rewrite the
finite rational and real up-law Gram-entry sums accordingly. This is a
square-level result only: it chooses no signed Wigner symbol or phase and adds
no half-integer, nonzero-magnetic-index, general `3j`/`6j`/`9j`, orthogonality,
recoupling, or infinite-series theory.

The volume consolidates the eleven former standalone research notebooks into
six thematic syntheses, followed by the later primary-exposition gap register:
reusable probability/discrete/asymptotic engines, repeated integration, the
exact dyadic web, dyadic endpoint asymptotics, quantitative Thue–Morse
convergence, and inverse/small-argument saddle analysis. It preserves their
natural-language arguments, symbolic computations, numerical evidence,
warnings, citations, provenance, and explicit proof obligations without
allowing any of that material to be mistaken for the formalization-backed
primary exposition.

Some passages use already-formalized results as inputs. That does not certify
the subsequent deductions. Conversely, when one claim is promoted to the
primary exposition, adjacent exploratory material remains here until its own
exact proof obligation is discharged.

## Placement and promotion rule

A mathematical claim belongs in the primary exposition only when a current
public Lean declaration proves the exact statement, including its domain,
normalization, hypotheses, endpoint convention, and conclusion or error term.
The declaration and its defining module must be recorded next to the claim or
in the primary document's audit map.

A related definition, a theorem with stronger hypotheses or weaker
conclusions, an executable computation, a paper citation, a numerical match,
an `.olean` file, an agent report, or an apparently immediate derivation is not
an exact counterpart. Material supported only in one of those ways stays in
this volume, however standard or plausible it appears.

Promotion is claim-by-claim:

1. Verify the exact Lean declaration in current source.
2. Integrate the supported material organically into
   [`Fabius_Function_and_Rvachev_Up.tex`](../Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex)
   without duplicating material already there.
3. Remove or relabel the matching frontier obligation while preserving every
   adjacent claim that remains unformalized.
4. Rebuild and inspect every affected PDF.

Research drafts are temporary inboxes, not archives. Once every part of a
draft has either been integrated into the primary exposition or preserved in
the canonical frontier volume, delete the processed draft. Delete the draft
directory itself when it becomes empty.

## Consolidation provenance

The unified source records a provenance banner and the historically supplied
SHA-256 value for every absorbed document. A printed checksum is provenance
metadata, not a formalization claim; where no reachable repository blob
reproduces it, the canonical TeX labels it explicitly as unverified rather than
silently treating it as authenticated. The source snapshots consolidated on
25 August 2026 were recorded as follows:

No live `SHA256SUMS` or `SHA256SUMS.*` manifest is maintained; the inline
values below are historical provenance receipts only.

| Former source | SHA-256 |
| --- | --- |
| `Fabius_Dyadic_Formulae_and_Alternative_Representations/Fabius_Dyadic_Formulae_and_Alternative_Representations.tex` | `462276b10fcd32b0446deb7cfedc4ec07c2ae55dbd333d5ff9b1d98f07df89e1` |
| `Fabius_Dyadic_q_Connections/Fabius_Dyadic_q_Connections.tex` | `81a0a911ac7ab28e12c6b87ccaf76ffccaf32e48f873abff18fb7a2d01bcf3e5` |
| `Fabius_Dyadic_Asymptotic_Bridge/Fabius_Dyadic_Asymptotic_Bridge.tex` | `c5ad7c5298d958ab63f459a3e246c2293d3020525223bc05ef2d0e1edab58f10` |
| `Fabius_Dyadic_Formulae_to_Asymptotics/Fabius_Dyadic_Formulae_to_Asymptotics.tex` | `6e98efd3afc402159a7f080e8604c951d5bc51be4a73383da67c1241d46d54ca` |
| `Fabius_Integration_Research_Frontiers/Fabius_Integration_Research_Frontiers.tex` | `21222ae5a8c64cf556dac562fd66943ae0b6ed881408e23e37edfa9113bdecbd` |
| `Fabius_Inverse_and_Saddle_Research_Frontiers/Fabius_Inverse_and_Saddle_Research_Frontiers.tex` | `f9d8605761aaaa1b2c2af83e3c5c55dcd6acfc847402163458b03b68c7b35ff8` |
| `Fabius_Thue_Morse_Convergence_Rate/Fabius_Thue_Morse_Convergence_Rate.tex` | `577c5f3426def68a774fedf3fce61552d32200c8da526ace44178f2a8995a6d3` |
| `Fabius_Thue_Morse_Convergence_Rate-2/Fabius_Thue_Morse_Convergence_Rates.tex` | `384d69b461cb94af33f1c080703e269ea77104405d1940413f1944172b3312c0` |
| `Repeated_Integration_and_Rvachev_Up/Repeated_Integration_and_Rvachev_Up.tex` | `eadcb4b414ac93723a91acbd5062d44340f78134a2cecbc18f7d7ba67eb2c9be` |
| `Rvachev_Up_from_Repeated_Integration-2/Rvachev_Up_from_Repeated_Integration.tex` | `fad16072df30d9e6eb5df03da57dd217769180730581f1dfd19fa5be0d16b262` |
| `Small_Argument_Asymptotics/Small_Argument_Asymptotics.tex` | `85f51a20fc7b6bdf3b1d049ec4506f508aee3c4cd70554e6a68cbcc30977cb0b` |
| `Primary_Exposition_Gap_Register/Primary_Exposition_Gap_Register.tex` | `06c7b888d9601b67ad7a5c0aee3f087d44d9ecaaa9abfb3bf3edfda4bd29c0d1` |

The eleven notebooks are represented by six thematic syntheses, followed by
the post-audit gap register. Overlapping dossiers were merged around their
stronger backbones: independent derivations, sharper later statements, distinct
warnings, numerical data, figures, and useful provenance remain, while
genuinely redundant repetitions are compressed and cross-referenced. The
recorded checksums identify the intended absorbed snapshots subject to the
verification qualification above; subsequent synthesis and status corrections
are tracked by Git history in the canonical source.

## Draft layout

The draft inboxes under [`drafts/`](drafts/) are grouped thematically
(2026-08-28): `rvachev_up_fourier_decay/` (the Fourier-decay corpus),
`thue-morse/`, `exponents-and-q-series/`, `spectra-and-arithmetic/`,
`integration-and-transforms/`, `inverse-and-sampling/`,
`representations/`, `frontier-compilations/`, `lambert-w/` (added
when four articles on the Lambert W function itself arrived), and
`series-and-transseries/` (added 2026-09-02 for packages about the
formal-series calculus itself), with new
archives arriving through `drafts/incoming/` (see its README for the
protocol).

The inverse group publishes the canonical source
[*Inverse Fabius Theory: Analyticity, Asymptotics, Computability, and Dyadic
Sampling*](drafts/inverse-and-sampling/Inverse_Fabius_Analyticity_Asymptotics_and_Computability/inverse_fabius_theory.tex)
([PDF](drafts/inverse-and-sampling/Inverse_Fabius_Analyticity_Asymptotics_and_Computability/inverse_fabius_theory.pdf)).
Its immutable extraction input is pinned at
`0a0cdabeb72a6f7d67cfdfb76d02a8f7381c7bf7`; all 194 source-result rows have
reviewed dispositions, all 88 files in the two superseded source subgroups have
asset dispositions, and the deduplicated asset inventory covers 55 retained
files. Eight checksum-ledger rows from the former 63-payload checkpoint are now
retired. The former package paths, source hashes, nested lineage, and recovery
revisions remain in the package's
[`PROVENANCE.md`](drafts/inverse-and-sampling/Inverse_Fabius_Analyticity_Asymptotics_and_Computability/PROVENANCE.md).
Its retained 134-page, 2,027,726-byte A4 publication has SHA-256
`22bc68d855ad04dde9654e9fbd20b3ba7f05a33e3c5df0e5b80bb8991c94b41d`.
The package README records that historical checkpoint's clean three-pass
build, font preflight, and visual inspection. The current purpose-specific
23-input source closure has SHA-256
`aedf007c2cd150b1f83de6d8996b4bf31e267b3dbcec2d5cd4720f5d92122bdb`
and postdates the retained PDF, so a fresh three-pass build is required before
source/PDF synchronization may be claimed. The reviewed concordance classifies
50 source rows as Lean-proved and 95 as human-proved frontier results. Its two
newest exact matches are the forced parity-selected superconvergence corollary
and the full Appell lattice-reproduction theorem, including its degree-`N+1`
selected-phase clause.

Later the same day the groups other than the Fourier-decay corpus were
**consolidated into volumes**, in two styles: the original members were
merged mechanically — one document per group, absorbing the member
drafts verbatim with per-part label prefixes (the later second-wave
integral-transforms arrival was folded into that volume the same way,
as Part XII) — while the closely overlapping arrivals of waves two
through six were merged **editorially** into additional volumes
(`inverse-and-sampling/comb-interpolation/comb_interpolation_synthesis/`, the
former `inverse-and-sampling/inverse-asymptotics-and-computability/Inverse_Endpoint_All_Orders/`
now recorded as an input to the canonical inverse synthesis, and
`representations/Up_Polynomial_Synthesis/`): shared theorems stated
once with the best proof, unified notation, cross-source constants
verified, all source-specific material retained.  Waves seven through
thirteen (all 2026-08-28) were then absorbed into these standing
volumes rather than opening new ones: the lattice draft became a
chapter of `Up_Polynomial_Synthesis`; the two representation volumes
were unified into the single eight-part `Representation_Frontiers`;
the finite-sinc, Fourier-image, transport-geometry, and
atomic-splines reports became Parts III–VI of
`Exponents_and_q_Series_Frontiers`; and the three
Euler–Maclaurin/exhaustion/phase reports were merged editorially into
the comb volume's Bernoulli-periodization section, where the
consolidation itself settled six previously open items (the spectral
positivity D(2r) > 0, the twisted positivity at every odd scale with
its Thue–Morse sign law, both phase-classification conjectures, the
alternating Bernoulli-moment sign law, and the odd half of the sharp
threshold).  The fourteenth and fifteenth waves — a second and a third
independent reconstruction of Rvachev's atomic-functions chapter —
were merged editorially into that volume's Part VI, adding the
fractal-string/tube-formula geometry, the local-degree law with its
critical exponential limit, quantitative Gaussian and uniform
parameter limits, the exact general-base Gamma–zeta Laplace
decomposition (settling the transform-level half of the
periodic-Lambert conjecture), the two Fup hierarchies (the canonical
ladder and the classical narrowing family with its triangular
reconstruction and Gaussian regime), signed gap leading coefficients,
derivative equimeasurability with the full L^p ladder, and the edge
pantograph equations.  The sixteenth and seventeenth waves — same-topic
twins on the signed/reciprocal parameter orbit of the geometric-uniform
family — were merged editorially as that volume's Part VII, adding
affine sign conjugacy, reciprocal germ inversion with its
Laplace/vertical-line dual, geometric multisection, the two-nome
Pochhammer–Prouhet partition function, the exact inverse-geometric
endpoint lattice with its jets and two-term asymptotics, and the
resolution of the periodic-cocycle conjecture via Part VI's exact
Laplace decomposition.  Eight revised or expanded editions of the atomic-functions
reports were then merged into Part VI, adding the spectral
Stieltjes–Wigert bridge, the distance-Mellin law, the q-Gaussian
derivative Gram geometry with theta-function Riesz bounds, the
log-Weibull jet-intermittency law, a proof of the Fup_n Edgeworth
register conjecture, then — from the audit-aware expanded editions —
the closed Gaussian-binomial Gram–Schmidt orthogonalization with its
Rogers–Szegő identification, the wrapped-heat-kernel circle model,
the MacMahon determinant constant with triple-product Riesz bounds,
the physical-space Stieltjes–Wigert differential ladder (identified
during the merge with the Gram–Schmidt vectors, a check that caught
and repaired a sign-convention slip in that theorem's first
printing), the derivative-jet Gram determinants, the autocorrelation
germ with zero Taylor radius, the exact derivative-energy
factorization with its Bernoulli-convolution limit and entropy laws,
the nodal-polynomial and exact-inverse closure of the orthogonalization
with its minimum-phase theta whitening filter, the Schur-minor strict
total positivity of the derivative Gram kernel, the two-term jet tail
with its sharp Orlicz threshold, the highest-jet partial-theta law with
the joint jet–distance transform, and eight register conjectures
(overlap-regime theta and energy, explicit spectral null modes, infinite
dual tower, finite-section boundary layer, centered staircase limit set,
partial-theta recreation of the complex dimensions, and graph-directed
Gaussian-binomial prediction).  For provenance the first of
these editions shipped the Russian source scan itself; the scan and
the raw OCR were deleted once their recoverable content was merged
and verified against the volume (SHA-256 hashes stay in the volume's
provenance list; git history archives the files; two later editions
re-shipped byte-identical copies, likewise not retained).  A new
`lambert-w/` group collected four independently written articles on
the Lambert W function itself; they were merged editorially into the
single consolidated volume `Lambert_W_Guide/` (the most complete
treatment as the body, the other three's unique layers in a
complements section, a four-way concordance, and a corpus-role
section tying W₋₁ to the endpoint theory).  Six polynomial-logarithmic
transseries articles that arrived on 2026-09-01 were filed in that group
too, since Lambert W is their guiding example; because their subject is
the transseries calculus rather than the function, they were regrouped on
2026-09-02 into the new `series-and-transseries/` group, under its
`polynomial-logarithmic-transseries/` subgroup.  That move was verbatim —
no source or PDF changed — and the same day the six were merged editorially
into the single canonical volume *Polynomial–Logarithmic Transseries:
Algebra, Composition, Series Reversal, and the Lambert W Archetype* (412 A4
pages).  None of the six was a superset of the others and each contributed a
layer no other supplied, so the merge kept every distinct result and collapsed
only repetition.  Every statement in the volume carries a proof: where a source
asserted a result without one it was supplied, and where a source claimed
analytic validity on the strength of formal algebra the claim was weakened to
what the algebra establishes, each repair marked at the point of repair and
collected in the volume's ledger.  Its formalization register records what the
Lean corpus does and does not cover, distinguishing a formalized *neighbour* —
the corpus proves Lagrange inversion and the Lambert series at the **origin**,
while this volume works at **infinity** — from actual coverage.  The absorbed
directories were deleted after a residue audit.  By the same precedent, a
standalone reference monograph on q-Pochhammer symbols and q-binomial
coefficients — the machinery consumed by the exponents
volume's Parts II/VI/VII and the formalized Gaussian-binomial core —
was filed as a second member of `exponents-and-q-series/` rather than
merged into the frontier volume, after an on-arrival audit (symbolic
re-verification of its core theorems, 30-digit numerical checks of
its two newest identities, one repaired majorant).  Initially 96 pages, the
post-consolidation monograph now has 212 A4 pages. Several volumes'
part-boundary section numbering and
page-counter handling were repaired along the way (edits are marked
`% ed.:` in the sources).  Every volume carries
a provenance section with each absorbed member's SHA-256; the absorbed
directories were deleted (git history is the archive). The Fourier-decay
corpus initially stayed separate so its independent reports could be audited;
on 2026-08-31 it too was consolidated, editorially, into one corrected proof
volume. Its source concordance and immutable pre-consolidation Git links retain
that audit evidence without leaving superseded documents live (see its README).
Each group carries a
`README.md` stating its purpose and contents, and
[`drafts/MANIFEST.md`](drafts/MANIFEST.md) is the global inventory:
every volume with its title and the previous paths of what it
absorbed. Path strings *inside* the documents predate the grouping and
are resolved through that manifest; the mechanical steps changed no
member's mathematical content, and the editorial merges record their
deduplication decisions in their provenance appendices.

## Maintenance

New unformalized mathematical write-ups must be merged into the canonical
LaTeX volume rather than retained as permanent parallel dossiers. A temporary
subdirectory may serve as an inbox during concurrent work (placed in the
matching thematic group above, and added to `drafts/MANIFEST.md`), but it
must be audited, absorbed, and removed promptly — updating the manifest and
group README on removal.

### Consistency audits

The scripts under [`scripts/`](scripts/) check the volumes and module
documentation against the Lean corpus. `scripts/audit_all.sh` runs all four
hard checks and exits nonzero if any hard check fails; run it before pushing
any change that touches either side. The stale-claim and crosswalk-coverage
surveys are advisory; the build-log checker is run separately after compiling
a changed volume.

- `scripts/audit_facade_reachability.py` — every module on disk is reachable from the
  library root `FabiusFunction.lean`. A newly added leaf module that nothing
  imports is never elaborated by `lake build FabiusFunction`, so a whole-library
  build would report success while silently skipping it.
- `scripts/audit_crosswalk_names.py` — every `Fabius.*` name cited in a `.tex` file
  resolves to a declaration or a namespace that exists in the corpus. The
  corpus is scanned with a namespace stack, so dotted citations such as
  `Fabius.SaddleExpansion.expCoeff` are matched whole rather than truncated at
  the first dot. A citation that no longer resolves usually means a Lean
  declaration was renamed without its crosswalk being updated.
- `scripts/audit_duplicate_names.py` — no two modules declare the same non-private,
  fully qualified name. A collision generally means that a new module has
  reproved an existing result and should import it instead.
- `scripts/audit_docstring_names.py` — backticked identifiers advertised in bulleted
  module-docstring declarations resolve in the corpus. An unresolved
  `Fabius.*` name is a hard failure. An unresolved unqualified name is advisory
  only, because it may be a root-namespace Mathlib declaration that this
  lexical audit cannot distinguish from a stale local name.
- `scripts/audit_stale_claims.py` and `scripts/audit_crosswalk_coverage.py` — advisory worklists
  for contradictory “open” claims and theorem environments lacking either a
  nearby Lean citation or an explicit formalization disclaimer.

The four hard checks have no standing exceptions. If one starts reporting a
failure that looks spurious, fix the script rather than carrying the exception:
the three false positives the crosswalk used to report were hiding about ninety
citations that were only being checked at their first component. Docstring-name
advisories are printed for review but intentionally do not change the exit
status.

`scripts/audit_overfull.py <file.log> [threshold_pt]` is a separate post-build
helper, not part of `scripts/audit_all.sh`: it parses both horizontal excess widths and vertical
excess heights without the shell-escaping ambiguity of the old `grep` pipeline,
and exits nonzero above the chosen threshold.  Output-routine vertical boxes,
which carry no source-line range in a LaTeX log, are reported explicitly rather
than mistaken for a checker failure.

Build the canonical document with exactly three `pdflatex` passes, inspect the
rendered PDF, and commit the PDF with its source. A coordinator may authorize a
source-only feature-branch checkpoint for semantic review before the rebuild;
such a checkpoint is never promoted to `main`. Before integration into
`origin/main`, the matching rendered PDF must be rebuilt, inspected, and
committed. Never advance `main` with a TeX/PDF mismatch. Do not commit `.aux`,
`.log`, `.out`, `.toc`, or rendered page images.
