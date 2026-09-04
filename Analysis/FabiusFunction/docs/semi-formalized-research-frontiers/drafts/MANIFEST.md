# Draft manifest

Global inventory of every research draft under this directory, grouped by
theme. Each draft directory holds one source package and any supporting data,
scripts, or figures; most also retain a compiled publication PDF, while a
source-only package records that status explicitly. Drafts are **temporary
inboxes** (see [`../README.md`](../README.md)): once a draft's content is
either integrated into the primary exposition or absorbed into the
canonical frontier volume, the draft is deleted; this manifest must be
updated when that happens.

New drafts arrive through `incoming/` (as archives or directories),
are unpacked into the matching group, and are recorded here.

Reorganized into thematic groups on 2026-08-28. Path strings inside the
documents themselves (corpus inventories, provenance banners,
`\nolinkurl{...}` pointers) predate the reorganization and refer to the
old flat layout; the **Previous path** column below is the map. Documents
were moved verbatim — no `.tex` content was changed by the reorganization,
so no PDF was rebuilt for it.

**Current artifact checkpoint (2026-09-01).** The live Lean audit contains
exactly 671 facade-reachable modules and 8,859 public declarations, with no
missing module headers or declaration documentation. The latest PDFs are all
validated pre-union checkpoints and are historical pending rerender: the
189-page primary exposition (SHA-256
`de0fc11a0ee45cd5a8942385aea543ec456b869a09e560878b021363a657796c`),
the 150-page walkthrough (SHA-256
`970d9b7b988e48cbeb119cf0e4ecf3a865ee8c7f9a30ab9a523693943e601616`),
the 357-page q-series synthesis (SHA-256
`3673b2cb7d617ccbcc9e3c32af17dbb9f4e8d8c16882d889d2a299bd128e0593`),
and the 253-page canonical frontier (SHA-256
`cd2a099e1f517d17ca345a52cdac5753899364652223ed8b7802c52d38c2a299`).
They predate the current source union; the q-series and canonical-frontier
artifacts specifically render the preceding 659-module/8,769-declaration
checkpoint, not the later twelve-module/ninety-declaration extension.
Page counts below are publication
receipts, not claims that retained PDFs render the final merged TeX. Other
documented sequences include 167- and 177-page primary expositions,
126- and 136-page walkthroughs, 237- and 243-page canonical frontiers, a
377-page Integration master, 71- and 88-page notation-catalogue checkpoints,
a 301-page Representation master, a 41-page New Frontiers-2 checkpoint, a
42-page inverse-computability report, a 158-page comb synthesis, 335-, 340-,
345-, 347-, 348-, and 354-page q-series receipts, and 238-page Exponents renders. The
canonical inverse-theory PDF has not yet been published. Every live TeX that
advanced after its named render requires a fresh three-pass build before
source/PDF synchronization is claimed.

The notation-unification tranche completed on 2026-09-01 was source-only: no
PDF was regenerated.  For every affected package, the exact live-source
fingerprint recorded in the thematic checkpoint below supersedes an older
inline source count or any earlier statement that the retained publication PDF
renders the current TeX.  Immutable arrival records and all historical build
fingerprints remain provenance evidence rather than current-source claims.

The inverse-computability row below retains its detailed arrival history, but
its latest source-only checkpoint supersedes the older inline boundary: the
current report is 2,992 lines (SHA-256
`359ac1239788d1d7af25214a6be26e421f716db6d1c254692469bddd2d25833a`).
`EffectiveMonotoneInverse.lean` proves the certified fixed-depth
tolerant-bisection realizer and restricted sequential inversion, while
`FabiusInverseComputable.lean` proves the totalized inverse is an
`IsComputableRealFunction`. The retained 42-page PDF remains historical; the
exact ceiling modulus, gap-to-modulus abstract strengthening, and input-bit
asymptotics remain outside Lean.

The canonical q-series synthesis has distinct source/artifact receipts. Its
current TeX is a source-only successor to the retained historical 357-page A4
PDF, SHA-256
`3673b2cb7d617ccbcc9e3c32af17dbb9f4e8d8c16882d889d2a299bd128e0593`.
That artifact is the validated pre-union render for the 659/8,769 source union;
the earlier 348-page receipt remains provenance. The current source and
retained PDF are distinct payloads, so no render parity is claimed.

The live q-series topology records `RvachevPochhammerFactorization` as one
definition and ten theorems, `QPochhammerEntire` as zero definitions and five
theorems, `QPochhammerInfinite` as one definition and twenty-nine theorems,
`QMultinomial` as one definition and nine theorems, and
`GaussianBinomialPolynomialStructure` as zero definitions and five theorems.
The `RvachevPochhammerFactorization` inventory includes the unconditional
public bridge `complexQPochhammerInf_eq_qPochhammerInfIn`, including the
total-product junk-value regime.
The finite/infinite, q-calculus, identifiability, normal-convergence,
classical-limit, universal-polynomial, q-Taylor, partial-fraction, and
integer-index tranches remain exhaustively crosswalked.

The final two modules are `CentralQBinomialReduction.lean` (0+6), whose exact
surface is `finiteQPochhammerIn_mul_neg`, `finiteQPochhammerIn_two_mul`,
`finiteQPochhammerIn_map_ringHom`,
`central_gaussianBinomial_sq_mul_int`,
`central_gaussianBinomial_sq_mul`, and
`central_gaussianBinomial_sq_div`, and `CyclotomicFactorization.lean` (0+7),
whose exact surface is `div_add_div_le_div`,
`div_le_div_add_div_add_one`, `mem_range_and_mem_divisors_iff`,
`finiteQPochhammerIn_X_eq_prod_cyclotomic`,
`finiteQPochhammerIn_X_eq_gaussianBinomial_mul`,
`prod_cyclotomic_pow_div_extend`, and
`gaussianBinomial_X_eq_prod_cyclotomic`. The central multiplication identity
is division-free over commutative rings; only its quotient wrapper requires a
field and two nonzero denominators. The shifted-factorial cyclotomic theorem is
commutative-ring-level; the final Gaussian cancellation requires an integral
domain and retains `k ≤ n`.

The six post-factorization modules add four definitions and 46 theorems.
`PrimitiveRootBlock.lean` (0+3) consists exactly of
`gaussianBinomial_isPrimitiveRoot_eq_zero`,
`neg_one_pow_mul_pow_choose_two`, and
`finiteQPochhammerIn_isPrimitiveRoot`. They work over a commutative integral
domain at a primitive `d`th root; the interior zero assumes `0 < k < d`, and
the phase and complete block explicitly assume `0 < d`.

`QLucas.lean` (0+8) consists exactly of `two_mul_choose_two`,
`add_mul_add_sub_one`, `choose_two_add`,
`coeff_finiteQPochhammerIn_neg_X`, `finiteQPochhammerIn_neg_X_block`,
`coeff_block_pow_mul`, `pow_choose_two_add_mul_eq`, and
`gaussianBinomial_q_lucas`. The first three are natural-number identities and
the coefficient identities are commutative-ring-level. The block, phase, and
q-Lucas results use an integral domain, a primitive root, and `0 < d`; q-Lucas
also assumes `b,s < d`. Lean proves the evaluated primitive-root identity, not
a named polynomial congruence modulo `Φ_d`, so the manuscript q-Lucas row is
Partial pending the minimal-polynomial lift.

`CyclotomicDivisibility.lean` (0+3) consists exactly of
`cyclotomic_exponent_eq_one_iff`,
`cyclotomic_dvd_gaussianBinomial_iff`, and
`gaussianBinomial_mul_isPrimitiveRoot`. The carry and divisibility criteria
assume `k ≤ n` and `0 < d`, and divisibility is specifically in `ℚ[X]`. The
multiple-index root value uses a commutative integral domain and `0 < n`.
Together with the earlier exponent bound this closes the squarefreeness row,
but there is no separately named squarefree theorem. The Babbage row remains
Partial because the value, but not its derivative, is formalized.

`QCatalan.lean` (1+11) consists exactly of `map_qInt`, `qInt_X_monic`,
`qInt_X_natDegree`, `X_sub_one_mul_qInt`,
`qInt_X_eq_prod_cyclotomic`, `qInt_X_dvd_gaussianBinomial_rat`,
`qInt_X_dvd_gaussianBinomial_int`, the definition `qCatalan`,
`qInt_X_mul_qCatalan`, `qCatalan_natDegree`, `qCatalan_eval_one_mul`, and
`qCatalan_eval_one`. Ring maps commute with q-integers already for semirings;
monicity and degree use a nontrivial commutative ring. The noncomputable
`ℤ[X]` quotient is defined for every `n`, including zero, has degree
`n(n-1)`, and evaluates at one to the Catalan number. It asserts no
coefficient nonnegativity or unimodality.

`NewtonInterpolation.lean` (2+13) defines `newtonCoeff` and
`newtonInterpolant` and proves exactly `newtonCoeff_eq`, `newtonCoeff_zero`,
`newtonCoeff_mul_prod`, `newtonPoly_succ`, `eval_newtonPoly`,
`degree_newtonPoly_lt`, `newtonPoly_eq_interpolate`,
`eq_newtonPoly_of_eval_eq`, `coeff_newtonPoly_self`, `newtonCoeff_eq_sum`,
`nodal_range_pow`, `prod_erase_pow_sub_pow`, and
`newtonCoeff_pow_eq_sum`. This is finite interpolation over a field:
evaluation needs the relevant earlier-node difference product nonzero,
uniqueness and divided differences use finite-range injectivity, the geometric
basis needs `q ≠ 0`, and the coefficient sum needs injectivity of `j ↦ q^j`.
The `newtonInterpolant` name preserves the established scalar-sequence
`Fabius.newtonPoly` API; there is no topology or convergence theorem here.

`QBetaIntegral.lean` (1+8) defines the total real `qBeta` and proves exactly
`qNumber_pos`, `qBeta_term_eq`, `qBeta_eq_prod`, `qBeta_eq_qGamma`,
`qBeta_comm`, `qBeta_pos`, `qBeta_add_one_left`, and
`qBeta_add_one_right`. Evaluation, the q-gamma identity, symmetry, positivity,
and both recurrences require `0 < q < 1` and `x,y > 0`; term cancellation
requires `y > 0` with arbitrary real `x`. It supplies no complex continuation
or classical-limit theorem.

The final five q-series modules contribute 31 new public declarations.
`GaussianBinomialInteger.lean` (1+10) defines `gaussianBinomialZ` and proves
exactly `finiteQPochhammerIn_inv_base_eq`,
`finiteQPochhammerIn_mul_pow_inv_base`, `finiteQPochhammerIn_pow_div`,
`gaussianBinomialZ_zero_right`, `gaussianBinomialZ_natCast`,
`gaussianBinomialZ_succ`, `gaussianBinomialZ_succ'`,
`gaussianBinomialZ_neg_natCast`,
`hasSum_reciprocal_finiteQPochhammerIn`, and
`hasSum_reciprocal_finiteQPochhammerIn_neg`. The algebraic declarations are
over a field; inverse-base and integer comparison require `q ≠ 0`, quotient
and Pascal forms retain their displayed nonzero denominators, and the two
series require a complete normed field, `‖q‖ < 1`, and `‖z‖ < 1`, with
`q ≠ 0` additionally required for the negative-index series.

`GaussianBinomialComplexOrder.lean` (1+5) defines `gaussianBinomialC` using
the principal complex power and proves exactly `gaussianBinomialC_intCast`,
`gaussianBinomialC_natCast`, `hasSum_gaussianBinomialC_add`,
`hasSum_qPochhammerC_inv`, and `hasSum_qPochhammerC`. Integer agreement is
unconditional; natural agreement retains `q ≠ 0` and a nonzero finite
denominator. The first two series assume `‖q‖ < 1` and `‖z‖ < 1`; the last
assumes `q ≠ 0` and `‖z*q^α‖ < 1`.

`QPfaffSaalschutz.lean` (0+3) consists exactly of
`finiteQPochhammerIn_ne_zero_of_le`, `q_pfaff_saalschutz_term`, and
`q_pfaff_saalschutz`. The terminating field identity assumes nonzero
`q,a,b,c` and the four displayed nonzero finite-product denominators; the
term theorem additionally assumes `k ≤ n`. It has no convergence claim.
`QuantumMultinomial.lean` (0+5) consists exactly of
`sum_antidiagonalTuple_succ`, `gaussianBinomial_eq_evalRingHom_quantum`,
`gaussianBinomial_symm'`, `Commute.qMultinomial_left`, and
`quantum_multinomial`. Its ordered expansion holds in every semiring when
`q` commutes with each variable and `x_j*x_i = q*(x_i*x_j)` for `i < j`,
without centrality, ambient commutativity, division, or convergence.

`GaussianBinomialBounds.lean` (0+6) contributes exactly
`gaussianBinomial_inv`, `one_le_gaussianBinomial`,
`finiteQPochhammerIn_pow_le_one`,
`gaussianBinomial_le_inv_qPochhammerInfIn`,
`pow_le_gaussianBinomial_of_one_lt`, and
`gaussianBinomial_le_pow_div_of_one_lt`. Reciprocity holds over a field for
`q ≠ 0` and `k ≤ n`; the lower bound is ordered-field algebra for `q ≥ 0`;
the other bounds are real under the displayed `0 ≤ q < 1` or `Q > 1`
hypotheses. Positivity of `(q;q)_k` reuses the established
`GeneralQConditionNumber.finiteQPochhammerIn_self_pos` theorem rather than
redeclaring it. The module proves no asymptotic error term. Thus `prop:qbinom-growth`,
`prop:gaussian-bound`, and `prop:extreme-specializations` are Exact, while
`cor:qgreaterone` is Partial because only reciprocity is formalized.

The corpus-only `RvachevSuperconvergentSynthesis.lean` module (1+8) defines
`IsRvachevSuperconvergentPhase` and proves exactly
`isRvachevSuperconvergentPhase_two_pow_iff`,
`tsum_quarter_monomial_eq_integral_of_even_deg`,
`tsum_three_quarters_monomial_eq_integral_of_even_deg`,
`tsum_shifted_monomial_eq_integral_superconvergent`,
`tsum_shifted_polynomial_eq_integral_superconvergent`,
`integral_polynomial_mul_rvachevUp_eq_normalized_tsum_superconvergent`,
`normalized_tsum_shifted_rvachevDeconvolvedPolynomial_mul_rvachevUp_superconvergent`,
and `normalized_tsum_shifted_rvachevAppellPolynomial_mul_rvachevUp_superconvergent`.
For every nonzero natural mesh it selects the stated endpoint, half, or
quarter phases and proves exactness through degree `padicValNat 2 M + 1`,
physical quadrature, deconvolved reconstruction, and the Appell
specialization. It proves neither a complete phase classification nor
maximality, positivity, or rationality, and changes no q-series status row.

The outer spectral product's local-uniform convergence is exact for every
complex strict contraction, including `q = 0`, with dyadic Rvachev and
bounded-Fabius Fourier specializations. The compound centered/MGF and exterior
reciprocal/pole clauses remain Partial. The forward ledger covers 282 labelled
results: 90 Exact / 85 Partial / 99 None / 8 N/A interface rows. The seven
new Exact rows are the primitive-root block, cyclotomic squarefreeness,
q-Catalan, q-beta evaluation and recurrence, and the two geometric-Newton
rows. Q-Lucas and the Babbage derivative move from None to Partial for the
boundaries above. The evaluated q-Lucas theorem remains Partial because Lean
does not supply the minimal-polynomial lift to the manuscript congruence.
The independent 547-row source concordance remains 73 Lean-proved,
405 human-proved, 60 not applicable, and 9 conjectural rows.
No PDF was generated for this source-only update, so the retained 357-page
pre-union artifact remains historical. The comb synthesis separately
has a later chapter-03 notation edit: its retained 158-page, 2,456,105-byte
A4 PDF has SHA-256
`81d249c8b2bb124836c858bd8e0ef9c8764606a2f9655a798d69e7565b1759b4`;
it is a validated historical checkpoint pending a fresh three-pass render.

The q-series consolidation retired the three general guides, the former
forward q-Pochhammer monograph, and the former inverse-q driver after recording
their source dispositions. Their content and provenance now live in the single
root-level `q_pochhammer_q_binomial_monograph/`; every retired layout remains
recoverable from its pinned revision and Git history. The remaining standalone
q-series reports retain their thematic subgroup paths. In particular,
Exponents retains a 238-page, 6,953,898-byte PDF with SHA-256
`fa719a8ea68d3c474928b9fae7449f827eb35a5452613f2b660d8e88ba27267e`.
It is the three-pass historical artifact built from the preceding 16,274-line
source checkpoint; the live TeX advanced again through the semantic union.
Basic structural and font checks passed, but the larger batch stopped before a
fresh full log, page-box, and visual publication audit.  The exact historical
PDF fingerprint remains valid, while the live TeX intentionally has no current
fingerprint before its final-source rebuild and full validation.  The retired-analysis-
alias migration produced an intermediate 16,369-line, 737,768-byte source
checkpoint with SHA-256
`4313bddb87a0f248a8bad4bd5e5a7cfbb25da51d1b994abc0c9d4c62525ca78c`;
the live TeX advanced again through the later semantic union, so that
checkpoint is provenance rather than a current fingerprint.  Cyclotomic has a
1,875-line current source and a retained 28-page PDF; both packages require
final-source rebuilds before synchronization is claimed. Current TeX and
historical PDFs are distinct payloads; synchronization receipts wait for final
renders and validation.
Any older row below that calls one of these changed pairs synchronized, gives
Exponents as 236 or 237 pages, gives Cyclotomic as 29
pages/1,896 lines, gives the comb synthesis as 156 pages, or treats a retained
inverse/New-Frontiers PDF as current is superseded by this checkpoint. The
closed-form Gaunt/Wigner-square boundary recorded below and the q-jet status
in the linked q-series registry remain unchanged by this merge.

The Exponents history retains two source/PDF checkpoints without treating
either as the live pair.  The 16,279-line source checkpoint has SHA-256
`d8b23a27965e0d242708e441d69d9a41fa5c7ac41f8146f12645d08ef6765dfe`;
its retained 238-page, 6,317,278-byte A4 PDF has SHA-256
`113d0318216db3ceaab160d0d1024f7adb48193420c385e700a7dd34c698b7cd`.
A separate pre-replay source checkpoint
`2adbe7b1e450a858bb02e80e6b4c4c6420060733f2ae1fe25eb61b6546f58e0f`
produced a 238-page, 6,316,535-byte PDF with SHA-256
`df7b9ad69e0310b17988dd42cc22559cf22ff26027395c005c374ad51f9e62aa`;
the subsequent 16,344-line semantic-source checkpoint has SHA-256
`2c34d526f18379822ced4d807fd4049ecb85231f4a42a1cd2773fd3c990dd3b9`.
The currently retained Exponents PDF was rendered from another preceding
16,274-line, 731,692-byte source checkpoint with
SHA-256
`4be184dc95f7c9d7665e5edf56cd22dc66bdacbc2f113b03b700468836018f8b`.
The live TeX advanced after all of these receipts.  It includes exact
zero-order/exponent identifiability and constructive first differences plus
the final q-calculus/theta tranche, while zeta-quotient,
cumulant/analytic-sample, and probability-law identifiability remain Partial
in Lean. A current fingerprint is intentionally not asserted before the
source stabilizes and receives its pending rebuild validation. The retained
q-series and Exponents PDFs are
historical payloads; no live-source/PDF parity is claimed. These facts
supersede the older rows below.

## Incoming status

No research payload is awaiting intake.  The `incoming/` directory contains
only its permanent `README.md`; the six combinatorial archives and six
polynomial-logarithmic transseries directories received on 2026-09-01 are
recorded in their filed thematic groups below.

## fourier-decay — `rvachev_up_fourier_decay/`

The former twelve-document Fourier-decay corpus was consolidated editorially
on 2026-08-31. The canonical article deduplicates the original question, eight
reports, two audits, and the Gentle Guide; supplies missing proofs; corrects
the LIL normalization, Pochhammer formula, numerical transcriptions, and gauge
overclaims; and adds integer-ratio `q`-Pochhammer, ray, and variance theorems.
Its source concordance preserves the independent audit history through immutable
links to pre-consolidation commit `2e3567feb14947ee3ebcdab11adca64e746ad26f`.

| Directory | Document | Supporting evidence | Previous paths / provenance |
| --- | --- | --- | --- |
| `Rvachev_Up_Fourier_Decay/` | *Fourier Decay of Rvachev's Up-Function* — single canonical TeX/PDF synthesis, proof corpus, correction ledger, and Lean parity appendix | `verification_scripts/` retains the valid audit programs and captured data; the invalid legacy `stage4.py` sampler was retired in favor of `stage4b.py` | At commit `2e3567feb14947ee3ebcdab11adca64e746ad26f`: `asymptotic-decay-rate-of-an-infinite-product-of-sinc-functions/`;<br>`rvachev_up_fourier_decay-1/`;<br>`Rvachev_Up_Fourier_Decay-2/`;<br>`Rvachev_Up_Fourier_Decay-3/`;<br>`rvachev_up_fourier_decay-4/` through `rvachev_up_fourier_decay-8/`;<br>`Rvachev_Up_Fourier_Decay_Comparative_Audit/`;<br>`Rvachev_Up_Fourier_Decay_Second_Wave_Audit/`;<br>`Rvachev_Up_Fourier_Decay_Gentle_Guide/` |

## thue-morse — `thue-morse/`

| Directory | Document | Previous path |
| --- | --- | --- |
| `Thue_Morse_Atlas_and_Frontiers/` | *The Thue–Morse Sequence: Formula Atlas and Fabius–Rvachev Frontier Results* (137 pp) — consolidation (2026-08-28) of the former `Thue_Morse_Formula_Atlas/` (*A Unified Formula Atlas for the Thue–Morse Sequence*) and `Fabius_Rvachev_Thue_Morse_Frontier_Results/` (*A Finite-Block Calculus for the Fabius–Rvachev–Thue–Morse System*, heavily Lean-crosswalked); assets under `assets/`, provenance with SHA-256 in the document | absorbed drafts deleted; git history is the archive |

## combinatorial coefficient calculus — `combinatorial-coefficient-calculus/`

Six standalone archival arrivals were filed here on 2026-09-01.  Each package
preserved one submitted TeX/PDF pair byte-for-byte at intake and recorded both
payload fingerprints.  A later notation migration revised the sources only;
the retained PDFs remain the historical arrivals, distinct from the current
source payloads.  The manuscripts have visibly overlapping
subjects and titles, but comparison, deduplication, canonical selection, claim
review, PDF rebuilding, and Lean crosswalking are deliberately deferred until
after publication of this quick-gate intake.

| Directory | Document | Previous path / provenance |
| --- | --- | --- |
| `Combinatorial_Coefficient_Calculus-2/` | *Combinatorial Coefficient Calculus* — current 6,862-line/277,653-byte source (`0b4176a2…8c93f6`) and retained historical 147-page A4 PDF; both payload fingerprints were verified | `incoming/Combinatorial_Coefficient_Calculus-2.zip` (1,096,487 bytes; SHA-256 `a0ca605c1d3f1ee3e00eac1d69a8181e786dd414407a1b3b6db1a60f74d8766d`) |
| `Combinatorial_Coefficient_Calculus/` | *Combinatorial Coefficient Calculus* — current 6,873-line/276,828-byte source (`98497684…2ff63f`) and retained historical 143-page A4 PDF; both payload fingerprints were verified | `incoming/Combinatorial_Coefficient_Calculus.zip` (1,094,284 bytes; SHA-256 `a22479ac8f58e1710117af9d0a3f515c7d24ec250548f537520c9f9024f4321a`) |
| `Combinatorial_Formulae_and_Inversion_Theorems/` | *Combinatorial Formulae and Inversion Theorems* — current 7,036-line/283,111-byte source (`f070ad09…4670b3`) and retained historical 140-page A4 PDF; both payload fingerprints were verified | `incoming/Combinatorial_Formulae_and_Inversion_Theorems.zip` (1,101,493 bytes; SHA-256 `dae561780a4442a9f11acb7edf1ec508daca1db237db01fabf77c695ec924960`) |
| `Unified_Combinatorial_Coefficient_Calculus/` | *Unified Combinatorial Coefficient Calculus* — current 6,687-line/262,376-byte source (`9566ce29…8f8947`) and retained historical 144-page A4 PDF; both payload fingerprints were verified | `incoming/Unified_Combinatorial_Coefficient_Calculus.zip` (1,083,495 bytes; SHA-256 `c4217b088444eb3e4bf24a7542d360f02dfb8e240418b562a155ad0c251ab559`) |
| `Unified_Combinatorial_Formulae/` | *A Unified Calculus of Combinatorial Formulae* — current 5,898-line/232,717-byte source (`089c6ece…c81bb3`) and retained historical 130-page A4 PDF; both payload fingerprints were verified | `incoming/Unified_Combinatorial_Formulae.zip` (1,015,842 bytes; SHA-256 `611b14cfda15357b679a05d9586811d8fb39f6fe7d971f00424da2bb848a5594`) |
| `Unified_Combinatorial_Formulae_and_Inversion_Theorems/` | *Unified Combinatorial Formulae and Inversion Theorems* — current 6,610-line/257,216-byte source (`7f41ee4b…2417b2`) and retained historical 138-page A4 PDF; both payload fingerprints were verified | `incoming/Unified_Combinatorial_Formulae_and_Inversion_Theorems.zip` (1,062,893 bytes; SHA-256 `ba62d0653fba9f0d1d867885e0b45272ba128973c1e49938d6cb1f597b457e33`) |

## exponents-and-q-series — `exponents-and-q-series/`

The seven live document packages are organized by content. The canonical
`q_pochhammer_q_binomial_monograph/` is at this topic root; the other six are
grouped under `q-fabius-parameter-deformations/` and
`geometric-sinc-and-exponent-families/`. The former
`q-pochhammer-and-inversion/` locations are provenance-only and remain
recoverable from the pinned revisions and Git history; no live index remains.
The relative directories below name the current package locations; historical
arrival paths remain unchanged.

For the canonical q-series and Exponents packages, the exact source and
retained-artifact checkpoints above govern; older numbers embedded in the long
provenance rows are superseded and do not assert current source/PDF parity.

| Directory | Document | Previous path |
| --- | --- | --- |
| `q-fabius-parameter-deformations/Continuous_Parameter_Edgeworth_and_q_Gevrey_Frontier/` | *Continuous-Parameter Edgeworth Theory, Large Deviations, and Quadratic q-Gevrey Regularity at the Fabius--Rvachev Frontier* (29-page retained A4 PDF; 1,387 main-source lines at arrival and 1,372 currently). Landed 2026-08-30 in direct-arrival commit `52179f63fe955a64508915eedaa560de9f3056da` from the bare generic wrapper `drafts/incoming/Fabius_Rvachev_Frontier_Report_2026-08-30-G/` under this title-derived collision-safe name. Its manifest covers the full delivery; all 19 current payload hashes verified after three CSV payloads were normalized from CRLF to LF. Its title and abstract concern Edgeworth/deviation regimes, Lambert endpoint asymptotics, and quadratic-exponential Denjoy--Carleman regularity. It remains standalone pending post-publication claim and experiment review, comparison, and a Lean crosswalk; manuscript proof labels do not establish Lean proof status | `drafts/incoming/Fabius_Rvachev_Frontier_Report_2026-08-30-G/`; renamed and filed here |
| `q-fabius-parameter-deformations/fabius_q_frontiers_report/` | *Parameter-Flow, Gaussian, and Large-Deviation Frontiers for the q-Fabius--Rvachev Family* (23 A4 pp, 1,506 source lines; two scripts, four CSV tables, two captured outputs, and four PDF/PNG figure pairs). Landed 2026-08-30 as a bare directory in direct-arrival commit `8a184546747082cbd92ad4675fb61981c6b8c3b6`; no archive or outer hash was supplied. All 20 delivered payload hashes verified after four CSV payloads were normalized from CRLF to LF. All five PDFs are readable and unencrypted (27 pages total); its title and abstract concern q-transport, convex order, Gaussian/Edgeworth limits, large deviations, and a Lambert-W boundary. It remains standalone pending assessment, document-style normalization, comparison with the closely overlapping continuous-parameter report, and a Lean crosswalk; manuscript labels and numerical checks do not establish Lean verification | `drafts/incoming/fabius_q_frontiers_report/`; filed here and removed from the live inbox |
| `q_pochhammer_q_binomial_monograph/` | *q-Series and Inverse q-Analogs: A Proof-Oriented Synthesis* — the single canonical publication for forward q-Pochhammer, Gaussian, hypergeometric, theta, partition, Bailey, interpolation, Thue--Morse, and Fabius--Rvachev theory together with branch-aware inverse q-analogs, asymptotics, certification, and labelled frontiers. The former q-Pochhammer/q-binomial monograph supplies the forward backbone; the former inverse-q synthesis supplies its nine inverse chapters; and the three general q-series guides were reviewed as donor manuscripts, with repetitions collapsed into the strongest proved statement. The historical 260-row inverse theorem concordance, package/archive provenance, 77-row asset-disposition ledger, and unique reproducibility assets remain intact. `audit/MERGE_SOURCE_REVISION` separately pins the five-publication source surface used for this merge. The retained historical pre-union 357-page PDF is fingerprinted in the exact checkpoint above; the newer live source is a distinct payload whose final fingerprint is deferred until rebuild, so no render parity is claimed. Retained PDFs under `assets/` are research figures only. | Former live publications: `general-q-series-guides/q-series-proof-oriented-article/` (arrival commit `1360db6064c676f83bceb23bece5ed304dd09ce8`), `general-q-series-guides/q_series_from_first_principles/` (`c167e550348bfb33b4297684100d55dfb48b8c1a`), `general-q-series-guides/q_series_monograph/` (`1f0f98390d551725fc7d2274638dbd7de86ee346`), `q-pochhammer-and-inversion/q_pochhammer_q_binomial_monograph/`, and `q-pochhammer-and-inversion/inverse_q_analogs_and_series/`; all layouts remain recoverable from pinned revisions and Git history |
| `geometric-sinc-and-exponent-families/Cyclotomic_q_Fabius_Rvachev_Frontier/` | *Cyclotomic Blow-Ups and Natural Boundaries for the q-Fabius--Rvachev Sinc Product* (25 pp and 1558 source lines at arrival; currently 29 A4 pp and 1896 source lines, with a 577-line deterministic high-precision experiment, five CSV tables, two further generated data files, and four PDF/PNG figure pairs). Landed 2026-08-30 from `drafts/incoming/Cyclotomic_q_Fabius_Rvachev_Frontier.zip` (outer SHA-256 `029da7d9ec96a0b2e5c4164c37f2b361dd015112bd0c6237263e3c538c5b0f64`) in its own collision-safe wrapper. All 22 delivered payload hashes verified on arrival; five CSV payloads were subsequently normalized from CRLF to LF. Its title and abstract concern the complex geometric sinc product, radial root-of-unity expansions and a claimed natural boundary, cyclotomic blow-ups, Bell/moment condensation, and inverse frequency and q-branches. A post-publication revision crosswalks the global geometric-sinc q-Pochhammer factorization while leaving the cyclotomic asymptotic and natural-boundary layers manuscript-only; all 22 current payloads were hash-verified at that checkpoint. The current five PDFs have 33 pages in total (29 main plus four one-page figures). The main report remains Latin Modern with nine embedded/subset Type-3 figure-font rows, and the four standalone figures contain nine more; normalization remains deferred | arrived through `drafts/incoming/`; archive unpacked here and deleted |
| *(exact reship; no second directory)* | `drafts/incoming/Fabius_Rvachev_Frontier_Report_2026-08-30-E.zip` (outer SHA-256 `174bf733156cd874cf4f9321c6ab71ca44f311856cc01dc158ddf83dc00cf813`) was processed on 2026-08-30 as an exact reship of `Fabius_Rvachev_Frontier_Report/`: the same 15-file set, with every non-CSV, non-ledger payload byte-identical and all three CSVs identical after the repository's existing CRLF-to-LF normalization. Its submitted 13-entry ledger again verified but again omitted `README.txt`; only its ledger bytes differ from the filed normalized package. No redundant wrapper was created, and no claim-level reassessment or experiment rerun was performed | duplicate archive verified and deleted; existing filed directory remains canonical |
| `q-fabius-parameter-deformations/Fabius_Flat_Parameter_Response_Dynamics/` | *Flat Parameter Fronts, q-Susceptibility, and Smooth Dynamics: New Frontier Results in the Fabius–Rvachev System* (23 pp, 1792 source lines; with a 519-line deterministic exact/Monte-Carlo program, five CSV tables, and two PNG figures). Landed 2026-08-30 from `drafts/incoming/fabius_frontier_report_2026.zip` (outer SHA-256 `afdcf522589a7baad82c81a527c02dcc09e58455ab14c57a9c492e65563c647e`) and filed under a title-derived collision-safe directory. All 13 delivered payload hashes verified on arrival; five CSV payloads were subsequently normalized from CRLF to LF. The manuscript concerns parameter susceptibility and tangent measures, flat q-parameter fronts, transform/moment/Legendre response, and Schröder/Böttcher-style Fabius dynamics. All 23 A4/Type-1 report pages rendered cleanly; blank author metadata and a nearly empty final bibliography page remain document-policy work. It remains standalone pending post-publication assessment and a Lean crosswalk; its 23 nonconjectural labels, four conjectures, and three problems record manuscript status only, and none of the new layers is thereby Lean-verified | arrived through `drafts/incoming/`; archive unpacked here and deleted |
| `geometric-sinc-and-exponent-families/Fabius_Rvachev_Frontier_Report/` | *Negative Parameters, Reciprocal Bases, and the Gaussian Boundary* (26 pp, 1491 source lines; with a deterministic numerical script, three CSV tables, a generated TeX fragment, and three dual-format figures). Landed 2026-08-30 from `drafts/incoming/Fabius_Rvachev_Frontier_Report_2026-08-30.zip`; all 13 payload checksums verified. Its principal paper-level strands are the affine transport from negative to positive geometric-uniform parameters, finite reciprocal-base digit reversal, residue-class multiplication, real-base log-concavity and plateau phases, and the Gaussian boundary with explicit cumulants and Berry--Esseen control. It overlaps Part VII's signed/reciprocal q-Fabius layer and therefore remains a separate member pending a claim-by-claim audit and deliberate editorial merge; no Lean status is inferred from the report labels | arrived through `drafts/incoming/`; archive unpacked here and deleted |
| `geometric-sinc-and-exponent-families/Exponents_and_q_Series_Frontiers/` | *Exponent-Sequence and q-Series Frontiers* (retired-analysis-alias migration checkpoint: 16,369 lines, 737,768 bytes, SHA-256 `4313bddb87a0f248a8bad4bd5e5a7cfbb25da51d1b994abc0c9d4c62525ca78c`; the live semantic-union TeX is newer and its final fingerprint is pending; retained historical PDF: 238 A4 pp, 6,953,898 bytes, SHA-256 `fa719a8ea68d3c474928b9fae7449f827eb35a5452613f2b660d8e88ba27267e`; the live TeX intentionally has no current fingerprint before final-source rebuild and validation, so no source/PDF parity is claimed) — consolidation (2026-08-28) of the former `Fabius_Newton_Rvachev_Frontier_Report/` (*Exponent-Sequence and Newton-Basis Frontiers*, Lean-crosswalked) and `fabius_frontier_results/` (*q-Binomial Richardson Acceleration of Geometric Sinc Products*), joined the same day by the eighth-wave `finite_sinc_products_report/` (*Finite Dyadic Sinc Products and Piecewise-Polynomial Approximants to Rvachev's Up-Function*, from `drafts/incoming/finite_sinc_products_report_bundle.zip`) as Part III — exact truncated-power prefix formula with Thue–Morse jumps, sharp derivative plateaux, exact error law 2^(C(r+3,2)−1)/(9·4ⁿ), exact Kolmogorov 1/(9·4ⁿ), Bell–Bernoulli all-orders expansion, q=1/4 Richardson weights, uniform scale mixture X = R·U, positive Gauss/Radau/Lobatto tail quadrature with exact constants (incl. the previously open variance-matched positive 16⁻ⁿ scheme) — and by the two ninth-wave same-topic reports `Rvachev_Piecewise_Approximation_Fourier_Images/` and `rvachev_fourier_frontier_report/` **merged editorially** as Part IV (*Fourier Images of the Repeated-Integration Approximants*): master factorization F̂ₙ = Φ·A(2⁻ⁿt) with the transfer function A = sinc z/Φ(z), valuation-weighted canonical product with divisor 1−v₂(m), digit-sum zero counts and Thue–Morse sign law, exact Taylor radius 4π with dominant-pole asymptotics and arithmetic Darboux hierarchy, finite/limit zero filtration, sharp o(2ⁿ) relative window, conditioning thresholds π2ⁿ/4π2ⁿ, deconvolution impossibility, weighted-L^p and Sobolev all-orders laws, exact mean-square tails with sharp H^s threshold s<n+½, and positive atomic/dyadic/polynomial closure menus (16⁻ⁿ–256⁻ⁿ) complementing Part III's box mixtures; and by the tenth-wave `fabius_finite_products_frontier/` as Part V (*Finite Dyadic Sinc Products and Exact Transport Geometry of Rvachev Spline Approximants*): convex-order and peakedness chains, exact E\|X_N\| = 5/18 − 4⁻ᴺ/9, fixed single crossing of the density error at ±½, the exact metric collapse W₁ = d_K = 4⁻ᴺ/9, TV = 2·4⁻ᴺ/9, stop-loss = Zolotarev-2 = 4⁻ᴺ/18, W∞ = 2⁻ᴺ, the exact Thue–Morse call-potential spline, the positive-mixture no-go theorem (signed weights are structurally necessary for Richardson acceleration), entropy/Fisher monotonicity with I(u_N)<∞ ⟺ N≥3 and KL(u‖u_N)=∞, and conjectural weighted information/W_p expansions with the p≈2N transport crossover; and by the thirteenth-wave `atomic_sinc_splines_report_package/` as Part VI (*Atomic Sinc-Product Splines Beyond the Binary Point*): an English translation and frontier expansion of Rvachev's Chapter 3 on atomic functions — the geometric family h_a with ĥ_a = ∏ sinc(2πa⁻ʲξ), the zero-matching existence criterion for general atomic equations, closed cumulants κ₂ₘ = 2²ᵐB₂ₘ/(2m(a²ᵐ−1)) with Bell/Lambert-series moment calculus, weighted Prouhet identities and the full derivative hierarchy with exact norms a^{n(n+3)/2+1}/2^{n+1} (L¹: a^{n(n+1)/2}), the Cantor gap atlas for a>2 (dim_H = log2/log a, exact per-gap degree, one-branch symbolic localization, complete Taylor-germ trichotomy), the rational-power Strang–Fix reproduction theorem with Appell coefficient operator, log-Gaussian Fourier envelope, all-orders prefix expansion with r₁ = −1/(6(a²−1)) and exact leading norm a⁶/(48(a²−1)) (specializing to the binary 4/9 and 31/16200), the a↓2 collapse, the reconstructed uniqueness theorem, and the periodic-Lambert/double-scaling/lattice-obstruction conjecture register; Part VI was then **merged editorially** (2026-08-28) with its fourteenth-wave twin `Atomic_Functions_Beyond_Dyadic_Report/` (*Atomic Functions Beyond the Critical Dyadic Case*) — a second independent reconstruction of the same Rvachev chapter (identical readings on every commonly transcribed equation; shared translation/h_a core deduplicated, OCR ledger preserved in assets) whose distinctive layers became dedicated Part VI sections: the fractal-string geometry of K_a (geometric zeta ℓ₀^s/(1−2a^{−s}), complex dimensions D_a+2πik/log a with residues ℓ₀^{s_k}/log a, exact tube formula with continuous nonconstant one-periodic Minkowski profile ⇒ K_a not Minkowski measurable, explicit logarithmic average), the geometric local-degree law P(N_a=r)=((a−2)/a)(2/a)^r with E N_a=2/(a−2) and (a−2)/2·N_a → Exp(1) as a↓2 (identifying the first marginal of the critical double-scaling program), quantitative parameter limits at both ends (a↓1: standardized cumulants 3^m2^{2m}B_{2m}(a²−1)^m/(2m(a^{2m}−1)), λ₄=−(6/5)(a²−1)/(a²+1), first characteristic correction; a→∞: W∞ ≤ 1/(a−1), TV ≤ 1/(2(a−1)), exactly uniform core g_a=1/2 on |y|≤(a−2)/(a−1)), the exact general-base negative-Laplace decomposition Λ_a(u) = −(log u)²/(2 log a) + (log u)/2 + P_a(log_a u) + E_a(u) with 0 ≤ E_a(u) ≤ e^{−u}/((1−e^{−u})(1−e^{−(a−1)u})) and real-analytic one-periodic P_a whose Fourier modes are −Γ(−χ_k)ζ(1−χ_k)/log a, χ_k=2πik/log a (settling the transform-level half of the periodic-Lambert program, pinning the Lambert normalization c_a=√a·log a/2, and re-verified independently during the merge to 10⁻¹³–10⁻²⁸), the divisor-polynomial form of log M_a, and the canonical Fup ladder G_n → 2Up(2·) in every C^m (first rung of the factor-redistribution direction); and (same day) with its fifteenth-wave twin `Rvachev_Atomic_Functions_Report/` (*Atomic Functions, Rvachev's up-Function, and Smooth Cantor Splines*) — a third independent reconstruction (again identical shared readings; repairs ledger and crosswalk preserved in assets) contributing the signed gap leading coefficients L_ω = (−1)^{N₊(ω)}a^{(r+1)(r+2)/2}/(2^{r+1}r!) with fixed-point verification at a=3, the derivative equimeasurability theorem with the full L^p ladder ‖h_a^{(n)}‖_p = (a^{n(n+3)/2}/2ⁿ)(2/a)^{n/p}‖h_a‖_p and the exact derivative-value mixture law (atom 1−(2/a)ⁿ at 0 + fair-signed amplified copy), the endpoint jet-reduction remark with the Bernoulli→cumulants→moments→jets→gap-polynomials exact engine, the classical Fup_n hierarchy F̂up_n = sinc(t2^{−n−1})ⁿ·Û(t2^{−n}) with the exact triangular reconstruction of Up by n(n+1)/2 dyadic averaging steps (limit: the cosine-multiplicity product ∏cos(t2^{−r})^{r−1}), closed Fup_n cumulants (σ_n² = 4^{−n}(3n+4)/36) and the quantitative CLT (Berry–Esseen O(n^{−1/2}), standardized cumulants O(n^{1−m})), the edge pantograph equations g_a′(u) = (a²/2)g_a(au) and F_a′(x) = a²/(2(a−1))F_a(ax) generalizing F′=2F(2·), and three more register items (Fup_n Edgeworth, graph-directed atomic splines, pressure-function Taylor multifractal); then with the two **revised fourteenth-wave editions** (`Atomic_Functions_Beyond_Dyadic_Report-2/`, `-3/`) contributing the Orlicz/rearrangement form of equimeasurability (all a≥2, all 0<p<∞, exact rearrangement thinning (h^{(n)})*(t)=C_{a,n}h*(t/(2/a)ⁿ)), the **spectral Stieltjes–Wigert bridge** (the normalized Fourier energy of h_a has squared-frequency moments a^{n(n+2)}/2ⁿ — the scaled Stieltjes–Wigert sequence, moment-equal to lognormal N(2log a−log2, 2log a) yet a distinct density ⇒ explicit non-lognormal representing measures for an indeterminate problem, with exact q-Pearson equations, Hankel determinants c^{N(N+1)}q^{−N(N+1)(4N+5)/6}∏(q;q)_k, monic OPs, and a Nevanlinna–Pick register conjecture), the **Mellin law of the distance to K_a** (Δ =d ½ℓ₀a^{−N_a}V; E Δ^s with pole lattice D_a−1+2πik/log a — the complex dimensions shifted by −1; distribution function = the exact tube formula; critical logarithmic gap scale → Exp(1)), and — decisive for provenance — the **eleven-page Russian source scan itself** (`source_rvachev_scan.pdf`), against which the translation layers were checked; the scan and the raw OCR were both deleted once their recoverable content was merged and verified (SHA-256 hashes in the volume's provenance list, the deduplicated repair ledger in Part VI's concordance appendix, git history the archive); then with the **revised fifteenth-wave edition** (`Atomic_Functions_Rvachev_Report_Package/`) contributing the **q-Gaussian derivative Gram geometry** (normalized towers ψ_n=h^{(n)}/‖h^{(n)}‖₂ split into two orthogonal parity towers with exact stationary kernel ⟨η_j,η_k⟩=q^{(j−k)²}, q=1/a; Gram determinants det G_N=∏_{r≤N}(q²;q²)_r, pivots (q²;q²)_N, sharp Riesz bounds ϑ₄(0,q) ≤ symbol ≤ ϑ₃(0,q) — the derivative tower is a uniformly conditioned Riesz sequence), the **log-Weibull jet-intermittency law** (leading amplitude A=L_{N_a}: exact staircase tail P(A≥L_r)=(2/a)^r, log P(A>x)/√log x → −log(a/2)√(2/log a), all positive moments infinite, log-moments finite), and the **PROOF of the Fup_n Edgeworth program** (uniform on ℝ, all orders, after any fixed number of derivatives, exact-cumulant Bernoulli–Hermite coefficients λ₄,n=−18(15n+16)/(25(3n+4)²), λ₆,n=144(63n+64)/(49(3n+4)³); register conjecture resolved, replaced by the beyond-all-orders Stokes program); then with the **expanded fifteenth-wave edition** (`Atomic_Functions_Rvachev_Expanded_Report/`, from `drafts/incoming/Atomic_Functions_Rvachev_Expanded_Report.zip`; audit-aware — it explicitly marks the previously merged layers as inherited baseline, so only its new layer was merged) contributing the **closed q-Gram–Schmidt orthogonalization** ψ*_n = Σ_j q^{n−j}·[n,j]_{q²}·e_j with norms ‖ψ*_n‖² = (q²;q²)_n, explicit Cholesky factorization C G_N Cᵀ = diag((q²;q²)_r) and closed inverse Gram (G_N⁻¹)_{jk} = Σ_n q^{2n−j−k}[n,j][n,k]/(q²;q²)_n, the Rogers–Szegő identification q^n H_n(z/q;q²) of the orthogonalizers, the uniform-innovation corollary dist²(e_n, span before) = (q²;q²)_n ↓ (q²;q²)_∞ > 0, the **wrapped-heat-kernel circle model** (each parity tower is unitarily the monomial sequence in L²(𝕋, ϑ₄(θ/2,q) dθ/2π) — the wrapped heat kernel at time log a centred at θ=π; two more derivatives = multiplication by z), the MacMahon determinant constant det G_N = (q²;q²)_∞^{N+1}·𝔐(a⁻²)(1+O(Nq^{2N})) with parity-factored full-sequence determinants D_{2N} = (det G_{N−1})², D_{2N+1} = det G_N det G_{N−1}, triple-product Riesz forms A_a = (q²;q²)_∞(q;q²)_∞², B_a = (q²;q²)_∞(−q;q²)_∞² with a verified numeric table (A₂ ≈ 0.1211242080, B₂ ≈ 2.1289368272), and the overlap-regime theta conjecture (translated correlations for 1 < a < 2 → the same theta kernel unless a log-periodic cycle obstructs; reduces to two-term derivative-norm asymptotics); then with two **expanded fourteenth-wave editions** (`Atomic_Functions_Beyond_Dyadic_Expanded/` and `Atomic_Functions_Beyond_Dyadic_Frontiers/`, both from `drafts/incoming/` zips, both audit-aware, both re-shipping byte-identical copies of the recorded source scan/OCR — again not retained) contributing disjoint new layers: the first the **physical-space Stieltjes–Wigert differential ladder** Υ_{a,n} = P_{a,n}(−d²/dx²)h_a (compactly supported orthogonal system with norms c^{2n}q^{−n(2n+1)}(q;q)_n‖h_a‖², explicit q-binomial expansion in even derivatives, three-term operator recurrence with α_n = cq^{−2n−1}(1+q−q^{n+1}), β_n = c²q^{−(4n−1)}(1−q^n)) — **identified during the merge with the expanded-15th-wave Gram–Schmidt vectors**, Υ_{a,n} = (−1)^n‖h^{(2n)}‖₂ψ*_n (a cross-edition unification; the check also caught and repaired a sign-convention slip in the first printing of the closed Gram–Schmidt theorem: the closed coefficients orthogonalize the raw tower, the sign-corrected basis takes alternating coefficients) — plus both parity **derivative-jet Gram determinants** (odd exponent −(N+1)(N+2)(4N+3)/6), the **autocorrelation germ** (−1)^n acf_a^{(2n)}(0)/acf_a(0) = a^{n(n+2)}/2^n with zero Taylor radius and provable ladder incompleteness (Riesz density criterion, spectral law absolutely continuous), and the explicit-spectral-null-modes conjecture; the second the **exact derivative-energy factorization** μ_{a,n,p} = Law(S_{a,n} + a^{−n}Y_{a,p}) (every normalized p-energy of every derivative = level-n Bernoulli address sum + compressed base profile) with W∞(μ_{a,n,p}, ν_a) ≤ 2a^{−n}/(a−1) to the symmetric **Bernoulli convolution** ν_a (uniform at a=2, equal-weight Cantor measure on K_a for a>2; Peres–Schlag–Solomyak cited), exact Hausdorff support rate b₁a^{−n}, exact **Rényi/Shannon entropy laws** H_β(n) = H_β(0) + n log(2/a) (0<β≤∞) with the critical entropy discontinuity and the information-dimension reading (address entropy n log2 / geometric scale n log a = D_a), and the overlap-regime derivative-energy conjecture (companion of the theta conjecture); then with two **expanded fifteenth-wave editions** (`Atomic_Functions_Rvachev_Report_Expanded/` and `Atomic_Functions_Rvachev_qBinomial_Frontiers/`, both from `drafts/incoming/` zips, both audit-aware; the first re-shipped byte-identical copies of the scan, OCR, **and the two previous editions of its own lineage** — all SHAs previously recorded, none retained) contributing four closures of the orthogonalization theory and two of the jet theory: the **nodal-polynomial reading** (residual generating polynomial P_n(z) = q^{n²}∏_{j<n}(z−q^{−2j}); orthogonality = interpolation at geometric nodes, pivot = value at the next node), the **exact inverse transform** η_n = Σ_k q^{(n−k)²}[n,k]_{q²} r_k with C′B = BC′ = I and the entrywise-positive Cholesky G = BDBᵀ, the **minimum-phase theta whitening** (innovation filters → a_r = (−q)^r/(q²;q²)_r in ℓ¹, A_q(z) = 1/(−qz;q²)_∞, exact identity |A_q|²·ϑ₃(θ/2,q) = (q²;q²)_∞ — the Szegő spectral factor of the q-Gaussian covariance; both editions' statements independently confirm the repaired sign convention), the **Schur-minor strict total positivity** (every mixed minor = q-power × Vandermonde × Schur polynomial > 0; oscillation-matrix and checkerboard-inverse consequences, Karlin cited), the **two-term jet tail** log P(A>x) = −γ_a√log x − (log(a/2)/(2 log a))·log log x + O(1) with the sharp Orlicz threshold E exp(θ√log A) < ∞ ⟺ θ < γ_a (boundary divergent), and the **highest-jet partial-theta law**: 𝒥_a = |h^{(N_a)}(Y)| has exact staircase tail with quadratic level inversion, reciprocal moments E𝒥^{−s} = p_a2^s a^{−s}·ϑ_p(2^{s+1}a^{−1−3s/2}; a^{−s/2}) (partial theta), and joint jet–distance transform whose s=0 limit degenerates to the distance-Mellin law — for s>0 the fractal pole lattice is replaced by an entire partial theta series; five new register conjectures (infinite dual tower with 1/ϑ₃ generating function, finite-section theta boundary layer, centered staircase limit set, partial-theta recreation of the complex dimensions, graph-directed Gaussian-binomial prediction) plus the transcendental-dichotomy sharpening of the algebraic-breakpoint conjecture; and by the sixteenth- and seventeenth-wave same-topic twins `Fabius_Q_Connections_Report/` (*Beyond the Dyadic Fabius Web*) and `Signed_Reciprocal_q_Fabius_Frontiers/` **merged editorially** as Part VII (*Signed and Reciprocal q-Fabius Frontiers*): the geometric-uniform family Y_q=(1−q)Σqʲ U_j on the full Klein-four orbit {q,−q,q⁻¹,−q⁻¹} — affine sign conjugacy Y_{−a} =d λ_a Y_a − β_a (λ_a=(1+a)/(1−a); no new normalized shapes at negative q), the reciprocal meromorphic germ with M_q(t)M_{1/q}(−t)=1 and finite digit-reversal duality Y_q^{[m]} =d Y_{q⁻¹}^{[m]} (giving q=±2,±4 exact finite/limiting meaning), geometric multisection Y_q =d Σ q^r/[m]_q·Y_{q^m}^{(r)} (Fabius = convolution of two quarter-base laws; u_{1/2}=u_{1/4}*2u_{1/4}(2·)) = Pochhammer dissection, the spectral q²-Pochhammer factorization ψ_q=∏_k((1−q)²t²/4π²k²;q²)_∞ with zero–pole exchange under inversion and base-b zero divisor 1+ν_b(n), cumulants κ_n=B_n/n·(1−q)ⁿ/(1−qⁿ) with spectral zeta ((1−q)/2π)^s ζ(s)/(1−|q|^s), log-concavity and the exact plateau phase |q|≤1/2 (crosswalked to Part VI's h_a plateau), the positive Laplace representation of reciprocal germs (moments on Re z=1/2, Hankel signature (−1)^{C(n,2)}, orthogonal polynomials with vertical zeros), the q-Fabius–Bernoulli Appell deconvolution family 𝔅_n^{(r)} (Bernoulli polynomials at r=0, centered monomials at r→1), the moment polynomial 𝒫_n(q)=(q;q)_n m_n/((1−q)ⁿn!) with degree C(n,2), boundaries 1/(n+1)! and B_n(1)/n!, and the odd-q-integer divisor conjecture ∏[d]_q | 𝒫_n (checked n≤16), the two-nome partition function Z_N(u,t;ρ,σ) unifying Gaussian layers and Prouhet cancellation (renormalized maximal Prouhet jet = the q-Fabius MGF; partial cancellations at root-of-unity nomes) plus the digit-position product Ξ_m(u,z;q) with position-parity companion χ(n) (4-state automaton), the exact q-Prouhet moment transfer S_{N,N+ℓ}=(−1)^N (N+ℓ)!/ℓ!·q^{C(N,2)}E T_{q,N}^ℓ ≡ general-radix Bell–Bernoulli, comb transport (sign=translation×parity, inversion=dilation), the Grassmannian/Hermitian finite-geometry square (Fu–Reiner–Stanton–Thiem) for both orbits, box-spline derivative combs with the quartic Cantor skeleton dim_H=1/2 and the comb factorization Δ_{q,2N}=Δ_{q²,N}*(D_q)_*Δ_{q²,N}, reciprocal q-Lagrange row reversal λ^{(q)}_{n,k}=λ^{(q⁻¹)}_{n,n−k}, the stop-loss simplex endpoint formula and exact inverse-geometric lattice G_q(qⁿ)=q^{C(n+1,2)}𝒫_n/(q;q)_n generalizing F(2⁻ⁿ) (new inverse-quartic values 1/6, 1/240, 1/51840, …) with all derivative jets G_q^{(r)}(qⁿ)=(1−q)^{−r}q^{−C(r,2)}G_q(q^{n−r}), the uniform two-term endpoint law log G_q = −ℓ²/2L − ℓ log ℓ/L + O(ℓ) and its √(2L log(1/y))−½ log log(1/y) inversion, and the RESOLUTION of the sixteenth wave's periodic-cocycle conjecture by Part VI's exact Γ–ζ Laplace decomposition (transform level closed uniformly in the base; density-level all-orders Lambert-W₋₁ transseries remains the shared open program, with the quartic phase conjecturally reconstructible from the dyadic one through decimation); the eighth-wave fold also repaired the volume's part-boundary section numbering; figures/data/scripts under `assets/` (absorbed source .tex files deleted after merging; SHA-256 provenance in the document) | absorbed drafts deleted; git history is the archive |



| *(all seven siblings merged and deleted)* | **The q-series sibling family is fully consolidated (2026-08-29).** Seven sibling drafts arrived through `drafts/incoming/` on 2026-08-28 — one 1106-line article-class survey and six book-class variants of 5663–6375 lines, all branched from the same monograph project, each appending its own "Fabius bridge". No sibling was a superset of the others (each carried 60–135 labels the rest lacked, out of 613 distinct new labels), so they were merged one measured pair at a time into `q_pochhammer_q_binomial_monograph/`, which grew from 96 pages; the sibling-consolidation snapshot was 210 pages (the later exact q=-1 crosswalk rebuild was 211 pages, and the current geometric-sinc crosswalk rebuild is 212 pages). Each was chosen as the closest remaining pair at the time: `q_pochhammer_q_binomial_monograph_bundle/` (0.942 against the filed monograph, its bridge part adopted wholesale); then `q_pochhammer_q_binomial_article-2/` with `q_pochhammer_q_binomial_monograph-3/` (0.680 against each other, merged jointly into the new Chapter 24, *Dyadic Gaussian–Thue–Morse structure and the values of F* — of monograph-3's 23 candidates, 4 were duplicates of article-2 items, 8 overlapped and are stated once in merged form, 11 were independent, and 7 of article-2's 10 items were absorbed); then `q_pochhammer_q_binomial_article/` with `q_pochhammer_q_binomial_monograph-2/` (0.588); and finally `q_pochhammer_and_q_binomial_coefficients-2/` (0.474), whose four bridge chapters contributed a ring-level residual principle valid over an arbitrary commutative ring with arbitrary weights and possibly repeated nodes, the exact formula on every dyadic cell, midpoint-centred truncations with an exact second-order rate, the off-grid continuation with its sharp uniform rate, the Appell polynomials of the Fabius law, and a digit-sparse Appell expansion at an arbitrary argument with exact residual; it also **corrected** a remark this monograph had adopted one merge earlier, on the admissible per-block shifts in the dyadic numerator. The 1106-line survey, `q_pochhammer_and_q_binomial_coefficients/`, was absorbed first and deleted last, once the two items deferred from it — the terminating ${}_2\phi_1$ reversal lemma and the classical limit of a nonterminating ${}_r\phi_{r-1}$ — had been integrated in corrected form. That third merge is the one that shows why the deduplication has to be re-run against the *current* monograph rather than the state the drafts were surveyed against: **15 of its 33 candidate results turned out to be already present**, nearly all of them in Chapter 24, which had not existed when those drafts were first examined. Of the rest, 1 was a duplicate of its own sibling, 10 overlapped an existing result and now replace it in strengthened form (notably the inverse-power value theorem, generalized from base 2 to every `0 < q < 1` **with the sharp threshold `q ≤ 1/2`** and strictness above it — a sharpness the monograph did not previously record), and 7 were independent. git history is the archive. (The first book-class sibling, `q_pochhammer_q_binomial_monograph_bundle/`, was **fully merged and deleted** on 2026-08-28: it was the closest pair in the whole `drafts/` tree by a wide margin — 0.942 combined label/section/theorem-name overlap with the filed monograph against 0.691 for the next pair — and after its bridge part was adopted, a residue audit found zero labels, sections, chapters, or atlas rows left in it, with the only remaining prose differences being places where the filed monograph is now strictly better. Its four genuinely unique paragraphs, the bridge reading-route signpost, the ProveIt/Zhong–Zhao/Eberl source-map paragraph, and the abstract's bridge clause, were carried across first.) | arrived through `drafts/incoming/` as six `.zip` archives and one bare `.tex`; the six archives were unpacked and deleted, the bare source was filed directly, and all seven sibling directories were deleted after absorption |

The old directory names, page counts, and uses of “current monograph” in the
preceding sibling-consolidation row describe its 2026-08-29 historical
checkpoint. That forward content now lives in
`q_pochhammer_q_binomial_monograph/` as part of the canonical synthesis listed
above.

## lambert-w — `lambert-w/`

The Lambert W function enters the corpus through the two-scale endpoint asymptotics and the phase-locked chain from `LambertPhaseLockedRichardson.lean` to the fixed-order analytic extractor `FabiusLambertPhaseExtraction.lean`; four independently written article packages on the function itself arrived on 2026-08-28 and were **merged editorially** into one volume.

The current compiled Lean crosswalk includes raw branch-point and full-domain continuity (`principalLambertW_continuousWithinAt_branchPoint`, `principalLambertW_continuousOn_Ici`, `lowerLambertW_continuousWithinAt_branchPoint`, `lowerLambertW_continuousOn_Ico`); the exact raw second-derivative formula, `W₀''(0) = -2`, full-domain principal strict concavity, and the lower branch's unique inflection at `-2 exp(-2)` with strict convexity through the branch point and inflection and strict concavity thereafter on the lower domain open at zero, all in `LambertWCurvature.lean`; generic phase continuity and exact interior second derivatives in `PowerExponentialLambertCalculus.lean` and `PowerExponentialLambertCurvature.lean`; the exact nonnegative-root iff `powerExponentialSaddle_eq_iff_eq_principal_or_eq_lower` with strict-interior distinctness `principalPowerExponentialPhase_ne_lowerPowerExponentialPhase`; and `PowerExponentialLambertAsymptotics.lean`, whose present scope is the principal-root equivalence, lower-phase divergence, and the intrinsic-epsilon two-term lower expansion.  The Fabius specialization also supplies the lower phase's exact inflection `2 exp(-2)/log 2`, strict convex/concave split, and the principal phase's strict convexity on the whole half-line ending at the peak through `PowerExponentialLambertFabiusCurvature.lean`.

`LambertWBranchPointGeometry.lean` has the exhaustive eight-theorem surface `tendsto_deriv_principalLambertW_branchPoint_atTop`, `tendsto_deriv_lowerLambertW_branchPoint_atBot`, `tendsto_principalLambertW_secantSlope_branchPoint_atTop`, `tendsto_lowerLambertW_secantSlope_branchPoint_atBot`, `principalLambertW_not_differentiableWithinAt_branchPoint`, `lowerLambertW_not_differentiableWithinAt_branchPoint`, `principalLambertW_not_differentiableAt_branchPoint`, and `lowerLambertW_not_differentiableAt_branchPoint`.  From the right of `-exp(-1)`, the principal derivative and endpoint secant slope tend to `+∞`, the lower counterparts tend to `-∞`, and neither branch has a finite right derivative or is differentiable there.

`LambertWBranchPointAsymptotics.lean` has the exhaustive one-definition/eight-theorem surface `lambertWBranchPointScale`, `lambertWBranchPointScale_pos`, `lambertWBranchPointScale_sq`, `tendsto_principalLambertW_add_one_sq_div_branchPoint`, `tendsto_lowerLambertW_add_one_sq_div_branchPoint`, `principalLambertW_add_one_sq_isEquivalent_branchPoint`, `lowerLambertW_add_one_sq_isEquivalent_branchPoint`, `principalLambertW_add_one_isEquivalent_branchPoint`, and `lowerLambertW_add_one_isEquivalent_branchPoint`.  The scale is `sqrt(2 exp(1) (z + exp(-1)))`, positive to the right of the branch point with square exactly `2 exp(1) (z + exp(-1))`; both squared ratios tend to `2 exp(1)`, both squared displacements have the corresponding asymptotic equivalence, and the signed leading laws are `W₀+1 ~ scale` and `W₋₁+1 ~ -scale`.

No finite endpoint derivative is asserted.  An `O(z + exp(-1))` remainder after the signed leading term, a convergent signed Puiseux expansion and its higher coefficients, named generic/Fabius phase wrappers for the derivative, secant, and square-root endpoint laws, the generic square-root threshold/strict-shape corollaries, a cleaned `L = log(A/x)` normalization, and the full generic asymptotic series remain open.

| Directory | Document | Previous path |
| --- | --- | --- |
| `Lambert_W_Guide/` | *The Lambert W Function: A Real-Variable Guide* (62 A4 pp, consolidated edition, 2026-08-28) — editorial merge of the four independent treatments: the spine is the most complete article (branches, identities, exact branch-pair parametrization with Bernoulli gap expansions, derivative polynomials, integral calculus with all polynomial moments and Mellin integrals on both unbounded ends, local Taylor, Maclaurin with proved Lagrange–Bürmann, tree function/Cayley, signed Puiseux at the branch point with recurrences, unified Stirling-number logarithmic asymptotics for both branches, rigorous elementary bounds incl. Chatzigeorgiou's W₋₁ bracket, Padé and Euler continued fractions, Kalugin–Jeffrey–Corless cut integrals with complete monotonicity of W₀′, residual-certified branch-safe logarithmic Newton with monotone global starts, transcendental-equation catalogue, applications, Wright omega, complex-branch guide, problems with solutions, formula sheet); a complements section preserves the other three treatments' unique layers — the complete power-tower convergence theorem (exact interval e^{−e} ≤ a ≤ e^{1/e} with two-cycle exclusion and neutral endpoints), x^y = y^x, inverse-Taylor/Schröder corrections with branch-aware seeds, the logarithmic fixed-point iteration criterion (attracting iff \|W\|>1), branch-exchange involution, scaling identities, fixed points 2πin, unwinding-integer logarithm identity, closed Lagrange form of the Puiseux coefficients, square-root monodromy, the transcendence theorem (W_k(algebraic ≠ 0) is transcendental), a practitioner's toolkit (parameter gradients with the (1+w)^{−1} factor, differentiate-in-w, parametrize-by-w, floating-point hazards), further applications (patch residence via W₋₁, Wien displacement, linear-drag fall time, Schwarzschild tortoise inversion, π(x) < x/W₀(x)), and the r-Lambert/generalized-Lambert outlook; plus a corpus-role section and a four-way concordance appendix (all shared constants verified identical); the packages' figures/data/scripts live under `assets/` (absorbed article .tex sources deleted after merging; SHA-256 provenance in the document) | absorbed member packages deleted; git history is the archive |
| `Polynomial-Logarithmic-Transseries-1/` | *Polynomial–Logarithmic Transseries: Algebra, Composition, Series Reversal, and the Lambert W Archetype* — current 4,020-line/187,071-byte source (`01a03e09…14f4e61`) and retained historical 119-page/584,392-byte custom-size PDF (`a4fc4af0…69e886`); both payload fingerprints verified | bare `incoming/Polynomial-Logarithmic-Transseries-1/`; direct-arrival commit `730e1763…95ab4f`; later source-only notation/remainder migration |
| `Polynomial-Logarithmic-Transseries-2/` | *Polynomial-Logarithmic Transseries: Arithmetic, Division, Composition, and Series Reversal* — current 5,006-line/173,396-byte source (`aa25baa0…8ef83e5`) and retained historical 102-page/571,108-byte custom-size PDF (`5e9ff596…bfc68e`); both payload fingerprints verified | bare `incoming/Polynomial-Logarithmic-Transseries-2/`; direct-arrival commit `730e1763…95ab4f`; later source-only notation/remainder migration |
| `Polynomial_Logarithmic_Transseries-3/` | *Polynomial-Logarithmic Transseries: Arithmetic, Composition, Series Reversal, and the Lambert W Expansion* — current 4,249-line/150,182-byte source (`0962c156…e6ad348`) and retained historical 87-page/510,663-byte Letter PDF (`3f7c4bc1…58a4af`); both payload fingerprints verified | bare `incoming/Polynomial_Logarithmic_Transseries-3/`; direct-arrival commit `730e1763…95ab4f`; later source-only notation/remainder migration |
| `Polynomial-Logarithmic-Transseries-4/` | *Polynomial-Logarithmic Transseries: Algebra, Composition, Reversion, and the Lambert W Function* — current 3,132-line/120,607-byte source (`387ca51f…32ff564`) and retained historical 47-page/428,534-byte A4 PDF (`c2d75b35…45a3eb`); both payload fingerprints verified | bare `incoming/Polynomial-Logarithmic-Transseries-4/`; direct-arrival commit `730e1763…95ab4f`; later source-only notation/remainder migration |
| `Polynomial_Logarithmic_Transseries-5/` | *Polynomial-Logarithmic Transseries: Algebra, Composition, Series Reversal, and the Lambert W Function* — current 2,443-line/106,141-byte source (`1149ae68…c8d26cc`) and retained historical 44-page/389,188-byte Letter PDF (`189e95ab…58a2db`); both payload fingerprints verified | bare `incoming/Polynomial_Logarithmic_Transseries-5/`; direct-arrival commit `730e1763…95ab4f`; later source-only notation/remainder migration |
| `Polynomial_Logarithmic_Transseries-6/` | *Polynomial–Logarithmic Transseries: Algebra, Division, Composition, and Asymptotic Series Reversal* (cover adds “with Lambert's W function as the guiding example”) — current 4,388-line/155,846-byte source (`df4e4bc5…47f8491`) and retained historical 100-page/701,319-byte A4 PDF (`b5142bad…467aa`); both payload fingerprints verified | bare `incoming/Polynomial_Logarithmic-Transseries-6/`; direct-arrival commit `730e1763…95ab4f`; later source-only notation/remainder migration |

The six retained arrival PDFs have embedded/subset fonts and no Type 3 font,
but none uses Libertinus; two are custom 522-by-738-point, two are Letter, and
two are A4.  Styling repair, comparison, claim review, consolidation, and Lean
crosswalking remain deferred until after the intake publication gate.

## spectra-and-arithmetic — `spectra-and-arithmetic/`

Current source counts for unaffected rows still supersede their older intake
figures below: Dyadic Radon Profiles has 2,050 lines and a 29-page main PDF;
Fabius Pascal Frontiers has 1,926 lines and a 26-page main PDF; Carleman
Frontiers has 1,934 lines; and Gamma Duality has 1,297 lines.

The notation-source checkpoint for the affected rows is exact: Digital
Spectral Geometry has 1,940 lines, 61,049 bytes, and SHA-256
`92d98914722f98b37f84a19283536c8b3925584d0729920b6346a4f572c735b1`;
Automatic Scale Factorizations has 1,682 lines, 62,490 bytes, and SHA-256
`3e40fef5247ed3d7263ff885dc97159b456f26347614817fc18e087af647de90`;
Holonomic Frontiers has 2,251 lines, 85,256 bytes, and SHA-256
`75f2a36ee0ae4b68e17030536cd7aa2cd922fea8941ed023afb272fafd29b20f`;
Reciprocal-Integer Convolution Divisors has 2,307 lines, 90,871 bytes, and
SHA-256
`e6e3d6df88efc3e50f7180b3853fdc6e4c9072f4e56192655bb76e195b282c4e`;
Total Positivity has 1,060 lines, 58,362 bytes, and SHA-256
`e7f05ac66a92284e82886bfe8b3376715ca0f71493a217d5a1adab6c17171475`;
and the consolidated Spectra and Arithmetic source has 8,183 lines, 349,076
bytes, and SHA-256
`683a560044772216980b05c4dd26957c6bbfb6c34019cc8d4cae815d9cff8df1`.
No PDF was rebuilt for these notation edits.  Their retained publication PDFs
remain historical build artifacts, and this checkpoint supersedes contrary
source counts, stale source/PDF parity language, or synchronization implications in
the long provenance rows below; arrival fingerprints remain unchanged.

| Directory | Document | Previous path |
| --- | --- | --- |
| `Digital_Spectral_Geometry_and_Log_Periodic_Saddles/` | *Digital Spectral Geometry and Log-Periodic Saddles* (24 A4 pp and 1,963 source lines at arrival; retained historical 24-page A4 PDF; current notation-source TeX: 1,940 lines, 61,049 bytes, SHA-256 `92d98914722f98b37f84a19283536c8b3925584d0729920b6346a4f572c735b1`; with a 490-line arbitrary-precision numerical program, a generated TeX fragment and summary, three generated PNG figures, and a reproducible 161-line repository-audit program). Landed 2026-08-30 from the rootless `drafts/incoming/Fabius_Rvachev_Frontier_Report_Package.zip` (outer SHA-256 `0028cb4f47134574ba7cd698bfc0ec11f08776b320cbc82b8467bea20d865f6d`) under a collision-safe title directory: the generic report stem is already occupied by the unrelated q-series member. The delivered manifest's TeX/PDF size and hash entries verified, but its repository audit had read **zero** TeX files and its numerical generation had failed. Intake repair preserved those arrival records, made the script compatible with current mpmath, regenerated all requested outputs at 80 digits and completed a recursive screen of 188 prior TeX files, 390,119 lines, and 16,813,357 bytes excluding this package directory (raw corpus digest `bb8a7de4c16a960f8d640d99797085b4f17cd0cdcc38b38caa4014536806b4d3`; cluster hits 43/88/36/24/75/37; `repository_audit.md` SHA-256 `70e66ec477a46666b3acfe5d81123ebf50576b92b4f9d25deb6cf6a93d27b5fb`). No theorem-level novelty is accepted on intake: the divisor/zeta/count/heat/cumulant spine specializes Exponents I and Frontier Compilations II/VII; the exact `K`/Lambert/base-b layer occurs in Exponents VI; Appell reproduction/first defect occurs in Exponents VI and `Up_Polynomial_Synthesis`; Legendre--Bessel occurs in `Representation_Frontiers`; sub-Gaussianity occurs in Frontier Compilations V; and the endpoint/inverse program has a stronger inverse synthesis. Only minor corollary-level residue remains to assess. The report's all-orders saddle and inverse statements were downgraded for a missing uniform remainder, global Strang--Fix sharpness was restricted to the proved canonical Appell defect, and the false strict-curvature range was corrected using the `b=2` center flatness and `b>2` plateau. Report labels convey no Lean status. `BaseDigitMultiplicity.lean`, `WeightedScaleMultiplicity.lean`, and `SpectralZetaWeighted.lean` now provide an exact seven-declaration finite arithmetic crosswalk, without proving the analytic zero multiplicities, canonical product, or complex spectral-zeta identity. The rebuilt PDF uses the current primary document's canonical A4 package, theorem, macro, boxed-environment, and listing-style block verbatim apart from permitted PDF metadata and running-head text; four required local notation commands follow it. Its Libertinus fonts are embedded and subset, with no Type 3 fonts. The retained historical 24-page A4 PDF is 852,061 bytes (SHA-256 `a87074c73f97d7040dbc1e5cd665e5214fcefecec64426441152caf306201dba`), and its build-source TeX was 60,274 bytes (SHA-256 `6612eaca5ba7f1a29c863cf4faf24904d0a991056dee747388c39a40fde14880`). The ten arrival payload hashes remain historical provenance; at the last fully validated checkpoint all 18 payloads verified (audit fingerprint SHA-256 `35fc6b627c4ef6a0bad20636747954b4ddad01a28d9b9a6a98957735663410d8`). This source-only merge invalidates the TeX, README, and validation fingerprints, which remain pending | arrived through `drafts/incoming/`; archive unpacked here and deleted after validation |
| `Automatic_Scale_Factorizations_Rvachev_2026-08-30/` | *Automatic Scale Factorizations of the Rvachev Law* (retained historical 22-page PDF; current notation-source TeX: 1,682 lines, 62,490 bytes, SHA-256 `3e40fef5247ed3d7263ff885dc97159b456f26347614817fc18e087af647de90`; with experiment, data, figures, and audits), committed directly to the inbox by `8a184546747082cbd92ad4675fb61981c6b8c3b6`. All 21 submitted payload hashes verified after six CSV payloads were normalized to LF and the JSON summary's missing final newline was repaired. It remains standalone pending comparison with the scale-factorization and spectral material already in the corpus; report labels do not imply Lean proofs | `drafts/incoming/Automatic_Scale_Factorizations_Rvachev_2026-08-30/`; filed here |
| `Dyadic_Radon_Profiles_Fabius_Rvachev_2026-08-30/` | *Dyadic Radon Profiles in the Fabius--Rvachev Web* (31 pp with experiment, data, figures, and audit), direct arrival `03b2f61889674f7d64ac86d3233236f5fa7ce660`. All 26 current payload hashes were verified after nine CSV payloads changed only from CRLF to LF. The zero-profile, Pascal, and digital-sign strands await claim-level comparison and Lean crosswalk | `drafts/incoming/Dyadic_Radon_Profiles_Fabius_Rvachev_2026-08-30/`; filed here |
| `Fabius_Pascal_Frontiers_Report/` | *Automatic Spectra, Exact Dyadic Cubature, and Probabilistic Duals in the Pascal--Rvachev hierarchy* (27 pp plus experiment/output payload), direct arrival `8a184546747082cbd92ad4675fb61981c6b8c3b6`. No hash manifest was supplied; all nine delivered files were independently hash-inventoried during intake. Its substantial overlap with the consolidated Pascal--Rvachev hierarchy is deferred to the required second phase; manuscript claims are not Lean status | `drafts/incoming/Fabius_Pascal_Frontiers_Report/`; filed here |
| `fabius_holonomic_frontiers_report/` | *Holonomic Rank, Exact Overlaps, and Non-P-Recursiveness* (retained historical 30-page PDF; current notation-source TeX: 2,251 lines, 85,256 bytes, SHA-256 `75f2a36ee0ae4b68e17030536cd7aa2cd922fea8941ed023afb272fafd29b20f`; with certificates, experiments, and figures), direct arrival `6d6737530ec541196c506f95ec20a701a29872b3`. All 26 current payload hashes verified after six CSV payloads were normalized to LF. Non-D-finiteness and non-P-recursiveness claims overlap the existing frontier corpus and remain unassessed at this intake stage | `drafts/incoming/fabius_holonomic_frontiers_report/`; filed here |
| `Fabius_Rvachev_Carleman_Frontiers_2026-08-30/` | *Critical Ultradifferentiable Geometry of the Fabius--Rvachev System* (24 pp with exact/high-precision experiment and figures), direct arrival `92c9909242ed6a2ab51d68ed816d1aa2a5339719`. All 21 current payload hashes verified after four CSV payloads were normalized to LF. Its derivative-growth and Carleman layers overlap the consolidated derivative-norm spectrum and same-batch q reports; comparison and formalization remain pending | `drafts/incoming/Fabius_Rvachev_Carleman_Frontiers_2026-08-30/`; filed here |
| `Dyadic_Spectral_Divisors_and_Gamma_Duality/` | *Dyadic Spectral Divisors and Gamma Duality* (22 pp with experiments, generated tables, and figures), direct arrival `d4605275f58f648ebcdeb74bc2ef5e4983abb6f0` under generic wrapper `Fabius_Rvachev_Frontier_Report-F/`. Its submitted three-entry hash list verified but omitted sixteen payloads; the repository intake audit recorded all twenty delivered files, including that submitted list. Zero-divisor, Laguerre--Polya, holonomicity, and moment claims remain separate pending semantic deduplication and Lean crosswalk | `drafts/incoming/Fabius_Rvachev_Frontier_Report-F/`; renamed and filed here |
| `Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors/` | *Reciprocal-Integer Convolution Divisors of the Rvachev Law* (retained historical 35-page A4 PDF; current notation-source TeX: 2,307 lines, 90,871 bytes, SHA-256 `e6e3d6df88efc3e50f7180b3853fdc6e4c9072f4e56192655bb76e195b282c4e`; with a 352-line exact/numerical experiment, six data files, four PNG figures, and a README). Landed 2026-08-30 from the rootless 14-file archive `drafts/incoming/fabius_rvachev_frontier_report_2026-08-30-B.zip` (outer SHA-256 `cfae82f303c3740bd76673fed772b1f69b9fedb0a911505360c930db7cc5a13f`). The repaired package has a title-derived pair, canonical A4/27 mm/Libertinus styling, deterministic LF CSV output, an exact three-pass build, and hash verification of all 14 current payloads; all fonts are embedded/subset, no Type 3 font or overfull box remains, and key pages and figures were inspected. Its reciprocal-integer characteristic quotients, scale classification, digit cocycle, parity theorem, transport and inverse bounds, arithmetic zero divisor, spectral zeta, Thue--Morse quotient, and Stern/hyperbinary specialization form a distinct arithmetic/spectral layer. Adjacent `GeneralizedZeroDivisor` and `ReciprocalIntegerGammaZeros` APIs are crosswalked without upgrading the quotient family to Lean status. A temp-isolated unpinned Python replay reproduced four CSVs byte-identically, the summary modulo EOL, and the endpoint CSV within `1.1102230246251565e-16`; Matplotlib layout drift is recorded. The package remains standalone pending claim-by-claim integration; manuscript theorem labels do not imply Lean status | arrived through `drafts/incoming/`; archive unpacked here and deleted |
| `Fabius_Total_Positivity_Frontier_Report/` | *Total Positivity and Cartwright Geometry in the Fabius--Rvachev Dyadic Sinc Product* (retained historical 24-page PDF; current notation-source TeX: 1,060 lines, 58,362 bytes, SHA-256 `e7f05ac66a92284e82886bfe8b3376715ca0f71493a217d5a1adab6c17171475`; with a 153-line numerical/symbolic experiment script, three generated PNG figures, one generated TeX table, and four CSV evidence tables). Landed 2026-08-30 as the bare three-file directory `drafts/incoming/Fabius_Total_Positivity_Frontier_Report/`; it shipped no README, hash manifest, environment pin, captured run output, or generated inputs. Arrival SHA-256 values are TeX `efea26060e6de63e97d00b982ca9e618f2234c88b8fd02f4ae9a8d63b7beecdd`, PDF `8f087969eaeb5eea349d64f6857f97356592c3464b9c3ecabcc9e5feec07630a`, and script `6674fa59e44fead9d41fb887e0634d8c363f816d1d2cceaf7886007db22d55fa`. The repository repair regenerated all eight missing outputs with the bundled script, normalized the source to A4/Libertinus, rebuilt it in exactly three passes with no Type 3 or overfull box, and added a README before hash-verifying all 12 current payloads. Its imaginary-square-root transform, Laguerre--Polya/PF-infinity and multiplier-sequence program, exact zero divisor and Thue--Morse sign interpolation, Cartwright geometry, and geometric-scale deformation belong to the arithmetic/spectral Fourier-product theme. Its novelty screen is materially stale even at its pinned snapshot: `Frontier_Compilations/` Part V already contains the matching Laguerre--Polya/PF-infinity/shifted-Jensen layer, with zero-count and sign material elsewhere in that volume; the source now records that correction and the exact finite general-base digit-count crosswalk, without promoting its analytic zero-order or sign claims. It therefore remains separate pending claim-by-claim crosswalk and deliberate deduplication; report theorem labels record paper-level status, not current Lean proof status | arrived through `drafts/incoming/`; bare directory filed and normalized here |
| `Spectra_and_Arithmetic_Frontiers/` | *Spectral Arithmetic Frontiers of the Fabius–Rvachev System* (current notation-source consolidated TeX: 8,183 lines, 349,076 bytes, SHA-256 `683a560044772216980b05c4dd26957c6bbfb6c34019cc8d4cae815d9cff8df1`; retained PDF predates it, so no render parity is claimed) — consolidation (2026-08-28) of the former `Fabius_Half_Integer_Spectral_Frontier_Report/` (*Half-Integer Spectral Arithmetic*), `Fabius_Arithmetic_Rays_Frontier_Report/` (*Arithmetic Dyadic Rays*), `Spectral_Arithmetic_Pascal_Rvachev_Hierarchy/` (*Spectral Arithmetic and the Pascal–Rvachev Hierarchy*), and `Fabius_Derivative_Norm_Spectrum_bundle/` (*Derivative Norm Spectra and Dual Moment Geometries*); assets under `assets/`, provenance with SHA-256 in the document | absorbed drafts deleted; git history is the archive |

## integration-and-transforms — `integration-and-transforms/`

| Directory | Document | Previous path |
| --- | --- | --- |
| `Integration_and_Transform_Frontiers/` | *Integration and Transform Frontiers for the Fabius–Rvachev System* (retained historical 377 pp, 12 parts) — consolidation (2026-08-28) of the former `Fabius_Antiderivatives_Report/`, `Fabius_Monomial_Antiderivatives_Report/`, `fabius_monomial_antiderivatives_report-2/`, `Fabius_Integral_Transforms_Report/`, `Fabius_Integral_and_Transform_Frontiers/`, `fabius_integral_frontiers_bundle/`, `Fabius_Rvachev_Integral_Frontiers/`, `Fabius_Integral_Transform_Fractional_Frontiers/`, `Fabius_Rvachev_Fractional_Integral_Report/`, `Fabius_Fractional_Integral_Transform_Frontiers/`, and `fabius_fractional_transform_frontiers_bundle/`, plus (folded in later on 2026-08-28 as Part XII by the same mechanical per-part step) the second-wave `Fabius_Integral_Transforms_Report/` (*Integral and Transform Calculus for the Fabius–Rvachev–Quantile System*: order-statistic spacings, beta–quantile lattices, dyadic resolvents, sinc energies, beyond-all-orders localization — an independent report sharing its directory name with Part IV's 2026-08-27 source); part order and former titles in the group README; assets under `assets/` (second-wave member under `assets/Fabius_Integral_Transforms_Report_second_wave/`), provenance with SHA-256 in the document | absorbed drafts deleted; git history is the archive |

## inverse-and-sampling — `inverse-and-sampling/`

The canonical inverse synthesis and the information-geometry intake live
directly in this group; the comb synthesis lives under `comb-interpolation/`.
The former `analyticity-and-elementarity/` and
`inverse-asymptotics-and-computability/` layouts survive only through the
pinned pre-retirement snapshot and the canonical provenance ledger.

`Inverse_Fabius_Analyticity_Asymptotics_and_Computability/` is now the
canonical-source synthesis of five retired inputs pinned at
`0a0cdabeb72a6f7d67cfdfb76d02a8f7381c7bf7`. Its master TeX inputs nine
chapter files. The reproducible raw source-result inventory passes 194/194
rows (projection SHA-256
`ff123825f7516adb1edfd9e738f9021d38c03960f0ea134554ede9e14cd8459f`),
and the reviewed `theorem_concordance.csv` preserves those ten immutable
source fields for all 194 rows. The structural validator passes with 748
labels and 588 references. Its current dispositions are 49 Lean-proved,
96 human-proved frontier results, 10 conjectures, 15 open problems, and 24
nonassertoric rows. In particular,
the centered Appell deconvolution, positive-degree Appell mean-zero, and
arbitrarily phased polynomial-deconvolution rows have exact named Lean
counterparts. The two newest promotions are
`is:p3:cor:forced-superconvergence` and
`is:p3:thm:Appell-lattice-reproduction`. The one-definition, eight-theorem
`RvachevSuperconvergentSynthesis.lean` module proves the parity-selected extra
degree for arbitrary nonzero natural meshes, its physical-coordinate
quadrature, deconvolved-polynomial synthesis, and the explicit
Rvachev--Appell specialization.
Eight inverse-computability rows are now exact as well: the main combined
theorem, the three tolerant-comparison certificates, fixed-depth bisection,
restricted sequential inversion, computable clamping, and the totalized
sequential corollary. The broader abstract inversion row remains human-proved
because the generic Lean theorem accepts a computable inverse modulus rather
than deriving it from the manuscript's positive gap sequence.
`ASSET_DISPOSITION.csv` accounts for 88 source-group files; the deduplicated
asset tree is present, and every retained payload was independently
hash-verified at that checkpoint. The retained 134-page, 2,027,726-byte A4 PDF
has SHA-256
`22bc68d855ad04dde9654e9fbd20b3ba7f05a33e3c5df0e5b80bb8991c94b41d`.
It is a fully reviewed historical checkpoint, not a rendering of the current
23-input source closure; a fresh three-pass build is still required before the
publication gate or source/PDF synchronization can be called complete. PDFs
from the five retired source packages or migrated as evidence are likewise
historical/source assets.

The comb row below is superseded in its publication receipt. The unchanged
driver SHA-256 is
`63fb8372dbcb6c0b27eb7dea19e387dea27af23811df9fcfbe9313d37c8180a4`,
but the later canonical-notation edit in `chapters/03_additive_dyadic.tex`
postdates the retained three-pass 158-page, 2,456,105-byte A4 PDF with SHA-256
`81d249c8b2bb124836c858bd8e0ef9c8764606a2f9655a798d69e7565b1759b4`.
That artifact passed the log, A4/page, text, metadata, font, render, and visual
gates for its recorded source graph. The updated source and retained PDF are
distinct payloads; a fresh three-pass render
is pending, and full numerical replay remains separate reproducibility work.

| Directory | Document | Previous path |
| --- | --- | --- |
| `Inverse_Fabius_Analyticity_Asymptotics_and_Computability/` | *Inverse Fabius Theory: Analyticity, Asymptotics, Computability, and Dyadic Sampling* — canonical editorial synthesis of five peer inputs. Its immutable extractor pin is `0a0cdabeb72a6f7d67cfdfb76d02a8f7381c7bf7`; all 194 source-result rows are dispositioned (49 Lean-proved, 96 human-proved frontier results, 10 conjectures, 15 open problems, and 24 non-applicable environments). The newest exact rows are `is:p3:cor:forced-superconvergence` and `is:p3:thm:Appell-lattice-reproduction`. `ASSET_DISPOSITION.csv` accounts for all 88 source-subgroup files, while all 63 retained payloads were hash-verified at the recorded checkpoint. Five post-snapshot results are classified separately in `LEAN_CROSSWALK.md`. The retained, fully reviewed PDF checkpoint has 134 A4 pages and 2,027,726 bytes (SHA-256 `22bc68d855ad04dde9654e9fbd20b3ba7f05a33e3c5df0e5b80bb8991c94b41d`). Its historical three-pass page, font, text, and visual gates and the independently checked current 23-input source closure are recorded separately in canonical `VALIDATION.md`; the source changed after that render, so a fresh build is required before synchronization is claimed. | At pre-retirement revision `93db15ad3c0645bd3cfd0a3e6e694e3c86a3aa2b`: `analyticity-and-elementarity/Non_Elementarity_of_the_Fabius_Function/`; `analyticity-and-elementarity/inverse_fabius_iterates_nowhere_analytic/`; `inverse-asymptotics-and-computability/Inverse_and_Sampling_Frontiers/`; `inverse-asymptotics-and-computability/Inverse_Endpoint_All_Orders/`; `inverse-asymptotics-and-computability/Inverse_Fabius_Computability_Report/`. Nested predecessors and arrival archives are recorded in canonical `PROVENANCE.md`; Git history is the byte-level archive. |
| `comb-interpolation/comb_interpolation_synthesis/` | *Comb Interpolation and Sampling Frontiers: Additive and Geometric Combs in the Fabius--Rvachev System* — canonical editorial synthesis of the former additive-dyadic volume and the three geometric-comb manuscripts. Shared Gaussian--Pascal, Jackson--Newton, Lagrange, stability, Fabius-boundary, quadrature, interpolation, modal, Mellin, regular-variation, spline, reciprocal-product, Euler--Maclaurin, Ruffa, and Thue--Morse material is deduplicated or preserved according to its exact source disposition. Its 180-file inventory and 151-row historical audit are complete; all 138 current package payloads were hash-verified at that checkpoint. The retained 158-page, 2,456,105-byte A4 PDF (SHA-256 `81d249c8b2bb124836c858bd8e0ef9c8764606a2f9655a798d69e7565b1759b4`) is a validated historical checkpoint; the current chapter-03 notation edit requires a fresh three-pass render before source/PDF synchronization is claimed. Full numerical replay remains separate reproducibility work. | Replaces `Dyadic_Comb_Frontiers/`, `geometric_comb_q_fabius_report/`, `geometric_comb_interpolation_report/`, and `geometric_comb_interpolation_report-3/`; original bytes remain in Git history. |
| `fabius_information_frontier/` | *Exact Information Geometry and New Frontiers for the Fabius--Rvachev System* (retained submitted 30-page A4 PDF; current 2,139-line TeX; a 601-line experiment, five data products, and three PDF/PNG figure pairs). The 18 arrival payload hashes and the later 19-payload audit distinguish the submitted PDF from later source changes. The information-geometry, entropy, Fisher-information, prefix-code, Thue--Morse, and endpoint layers remain archival manuscript claims pending hostile audit, numerical replay, an exact Lean crosswalk, canonical normalization, and rebuild; manuscript theorem labels do not establish formal verification. | `frontier-compilations/fabius_information_frontier/`; moved here by the thematic reorganization. |

## representations — `representations/`

Series and orthogonal-expansion representations of the up-function.
Current source counts for the unaffected documentation rows are 1,542 lines
for forward iterates, 1,913 for Stein--Koopman, and 1,318 for Noncommutative
Frontiers.  The exact notation-source checkpoint for the affected rows is:
Dyadic Chaos, 3,153 lines, 112,391 bytes, SHA-256
`34241042a005ea529219aca0761c121760a2574324bbb2300c365012cc1435c2`;
Zero Bias, 1,926 lines, 72,231 bytes, SHA-256
`5b0eb2cf61123d5c9a6bd7ec5fdef5f7f09b2130ea02e3437d54f6dac2e27e42`;
New Frontiers-2, 2,978 lines, 122,235 bytes, SHA-256
`e0015e424fe577c4aee3ea473ace71b67b9f250d5a96569dccd6dd03ebe20c98`;
and Shape/Divisibility/Stein, 2,057 lines, 83,124 bytes, SHA-256
`975ec7078562d88ba76c870ef1d90363380cbe422507762c305695b61f1c9bec`.
No PDF was rebuilt for these notation edits.  The associated PDFs remain
historical build artifacts; these fingerprints and that source-only boundary
supersede older counts and synchronization language embedded below, while all
arrival and historical build hashes remain unchanged.

| Directory | Document | Previous path |
| --- | --- | --- |
| `fabius_dyadic_chaos_frontier/` | *Dyadic Sensitivity and Polynomial-Chaos Frontiers for the Fabius--Rvachev Law* (34 pp at arrival; retained historical 40-page A4 PDF; current notation-source TeX: 3,153 lines, 112,391 bytes, SHA-256 `34241042a005ea529219aca0761c121760a2574324bbb2300c365012cc1435c2`; with a 672-line deterministic experiment, ten CSV/text products, six PDF/PNG figure pairs, and four audit files). Filed 2026-08-30 from `fabius_dyadic_chaos_frontier.zip` (1,351,045 bytes; SHA-256 `d57fd01c3991a6a7ecd6ba6e745729c745745d3265cb3cfd414aac1991b11b86`). All 30 submitted payload hashes verified at arrival; nine CSVs were normalized from CRLF to LF, after which all 33 current payloads were hash-verified. Post-intake review repaired the zero-field, infinite-product, Mellin-continuation, phase-limit, mode-set, Thue--Morse-domain, and Lambert-cutoff statements; replayed the deterministic experiment in two compatible environments; and rebuilt the 40-page report plus six one-page vector figures with embedded fonts and no Type 3 fonts. Its label-complete crosswalk inventories all 36 nonconjectural results. None is Lean-formalized exactly as stated, but `ThueMorseSymmetricDifference.lean` supplies the exact two-definition and eleven-theorem Boolean-cube, polynomial, dyadic-sign, and report-grid algebraic boundary of `thm:TM-corner`; the repeated `C^N` integral clause and final report-shaped wrapper remain open. The orthogonal-chaos report remains standalone pending broader comparison and deliberate integration; manuscript result labels do not establish Lean status | arrived through `drafts/incoming/`; archive unpacked here and deleted |
| `Fabius_Zero_Bias_Frontier_Report/` | *Zero-Bias Towers and Spectral Peeling for the Fabius--Rvachev Law* (retained historical 26-page A4 PDF; current notation-source TeX: 1,926 lines, 72,231 bytes, SHA-256 `5b0eb2cf61123d5c9a6bd7ec5fdef5f7f09b2130ea02e3437d54f6dac2e27e42`; with an 839-line reproducible experiment, six CSV tables, and five dual-format figures). Filed 2026-08-30 from `Fabius_Zero_Bias_Frontier_Report.zip` (1,300,870 bytes; SHA-256 `fb8bbf8e34a2f5eb4e5bbe7b06b22566502be7583696f01960a6e41d25b518ee`); its 21 arrival hashes and all 23 current payload hashes verified. Hostile intake review separates existing moment/Fourier/shape infrastructure from the paper-level zero-bias tower, collision-free occupancy, spectral peeling, and limiting claims. The canonical A4/27 mm/Libertinus report and regenerated figures contain no Type 3 fonts and were rebuilt in exactly three strict passes | arrived through `drafts/incoming/`; archive unpacked here and deleted |
| `common_digit_fabius_zonoids_frontier_report/` | *Common-Digit Fabius Zonoids: Exact Volumes, Hyperbolic-Secant Geometry, Bernoulli Gaussianization, and Parameter Jets* (36 pp with code and generated assets), direct arrival `fef364bfd162f80919cd77b808530dd0734f1cb1`. All 24 current payload hashes verified after six CSV payloads were normalized to LF. The multivariate/zonoid layer remains standalone pending comparison and a Lean crosswalk | `drafts/incoming/common_digit_fabius_zonoids_frontier_report/`; filed here |
| `Jacobi_Digit_Fabius_Rvachev_Frontier_Report/` | *Jacobi-Digit Deformations of the Fabius--Rvachev Law* (32 pp with experiment, data, and figures), direct arrival `92c9909242ed6a2ab51d68ed816d1aa2a5339719`. All 38 submitted non-ledger hashes verify exactly. This distinct representation family remains standalone pending mathematical assessment and Lean formalization | `drafts/incoming/Jacobi_Digit_Fabius_Rvachev_Frontier_Report/`; filed here |
| `Matrix_Dilated_Fabius_Rvachev_Frontier_Report/` | *Matrix-Dilated Fabius--Rvachev Laws* (29 pp with experiment, data, figures, and audits), direct arrival `8a184546747082cbd92ad4675fb61981c6b8c3b6`. All 27 current payload hashes verified after seven CSV payloads were normalized to LF. The self-affine box-spline/zonoid layer remains separate from the common-digit report pending a claim-level crosswalk; manuscript claims do not establish Lean status | `drafts/incoming/Matrix_Dilated_Fabius_Rvachev_Frontier_Report/`; filed here |
| `Fabius_Rvachev_Noncommutative_Frontiers/` | *Noncommutative Cumulant Frontiers for the Fabius--Rvachev Law* (26 A4 pp, 1336 source lines; with a 681-line exact/high-precision experiment, ten result files, three dual-format figures, a README, and minimum-version requirements). Landed 2026-08-30 from `drafts/incoming/Fabius_Rvachev_Noncommutative_Frontiers.zip` (outer SHA-256 `55f780d0780a693f2450fe6a4c8a63ba964b3d0e6fcea6d985040c6cb29e25cc`); all 21 payload checksums verified on arrival. The repository repair renamed the generic document stems, normalized four CSV writers and payloads to deterministic LF, selected PNG plot companions, adopted canonical A4/27 mm/Libertinus styling, and rebuilt the PDF in exactly three passes with all fonts embedded/subset and no Type 3 font; all 21 current payloads were hash-verified. Its free and Boolean moment transforms, exact non-free-infinite-divisibility certificates, q-parametric Hankel obstruction, Jacobi stripping and increment program, finite-sinc cumulant transfer, and inverse-Fabius/Legendre/endpoint interfaces form a distinct noncommutative representation layer, with spectral-arithmetic cross-links. No exact or semantic duplicate of that layer was found. It remains standalone pending a claim-by-claim Lean crosswalk and deliberate consolidation; report theorem labels record paper-level status, not current Lean proof status | arrived through `drafts/incoming/`; archive unpacked, deleted, and package normalized here |
| `Fabius_Rvachev_New_Frontiers-2/` | *Fabius--Rvachev New Frontiers: Log-concavity, Native Orthogonal Polynomials, Christoffel Reconstruction, Rational Products for Pi, Gauss--Pade Structure, and Legendre--Gaunt Determinants* (current source with a retained pre-update 41-page A4 artifact; with a 580-line exact/high-precision experiment, three CSV tables, five clean vector figures and five supplemental PNG companions, a corpus audit, publication log, and PDF preflight). Filed 2026-08-30 from `Fabius_Rvachev_New_Frontiers-2.zip` (SHA-256 `9e27257d8b2808c6f24c754e61fbf5ce7b997233d78d33a28536600665508108`); all 15 arrival payloads verified, and all 20 current payload hashes later verified. The current crosswalk inventories all 129 declarations in eleven Gram, rational-Jacobi, determinant, rational-value, finite-Gaunt, and zero-row-square modules while retaining Nevai, J-fraction, Hankel, and Gauss--Padé material as inherited overlap. Lean proves executable rational Gaunt integrals, exact Legendre product linearization over `ℚ` and `ℝ`, the total integer-index zero-row square datum with central-binomial and factorial forms, sharp parity/triangle support and positivity, and finite rational and real Wigner-square Gram sums. It does not define a signed/general Wigner symbol or phase. Roots, Christoffel reconstruction/products, quadrature, Padé identification, infinite Jacobi products, and asymptotics remain paper-only. The current notation-source TeX has 2,978 lines, 122,235 bytes, and SHA-256 `e0015e424fe577c4aee3ea473ace71b67b9f250d5a96569dccd6dd03ebe20c98`. The retained PDF was built from the former frozen source with SHA-256 `4eeea1a1cbe5497e6db3424a0c185f3a3be750f5816b22be5e7baed091753455`; exactly three strict passes (39/41/41 pages) produced the 780,141-byte PDF with SHA-256 `9871ac93cce5d8ee1aa48e946f46dc2e19865fb33a1d2e3b9b8be01360318901`. Its 35 font rows are embedded/subset, five are Libertinus, and it contains no Type 3 font or raster image. Extraction retains the historical 99 public names, including all 25 predecessor Gaunt names; the current source adds 30 closed-form/wrapper declarations not rendered there. Targeted visuals and all five vector figures pass; all 20 mixed source/retained-artifact payload hashes verified at that checkpoint. The earlier 39-page cleaned-vector and 41-page local Gaunt checkpoints remain documented as history | arrived through `drafts/incoming/`; archive unpacked here and deleted; current source/retained PDF pair intentionally unsynchronized pending rebuild; payloads hash-verified at the recorded checkpoint |
| `fabius_iterates_nowhere_analytic/` | *Nowhere Analyticity of Every Positive Compositional Iterate of the Fabius Function* (22 A4 pp, 1,566-line TeX; with a 469-line numerical diagnostic, four PNG figures mirrored between report/output directories, one CSV, metadata, README, and audit). Filed 2026-08-30 from `fabius_iterates_nowhere_analytic.zip` (SHA-256 `a1fbd4cf0a0fdd9479a2955bde0e7bcf5d4146032e4466916307826cfbe3bf0d`); all 14 arrival payload hashes and all 15 current payload hashes verified. The semantic union retains 15 nonconjectural results, two numbered warning quarantines, and one live defect-spectral-gap conjecture. `PartitionDefect.lean` formalizes three definitions and 33 finite list-arithmetic theorems, but the set-partition, weighted Bell/spine, tie, and n≥2 iterate layers remain manuscript-only. The canonical A4/27 mm/Libertinus PDF was rebuilt in exactly three strict passes with every font embedded/subset and no Type 3 fonts | arrived through `drafts/incoming/`; archive unpacked here and deleted |
| `Fabius_Rvachev_Shape_Divisibility_Stein_Geometry/` | *Shape, Divisibility, and Stein Geometry of the Fabius--Rvachev Law* (retained historical 34-page A4 PDF; current notation-source TeX: 2,057 lines, 83,124 bytes, SHA-256 `975ec7078562d88ba76c870ef1d90363380cbe422507762c305695b61f1c9bec`; with a 466-line numerical experiment, three CSV tables, four retained vector-PDF figures plus four PNG companions, readable diagnostics, Makefile, requirements, and README). Landed 2026-08-30 from `drafts/incoming/Fabius_Rvachev_Frontier_Report_2026-08-30-C.zip` (outer SHA-256 `200e65588b824d05f863ec0dae50b983408af3a7a2cf000c55556560e8e49d2e`); all 14 submitted hashes verified. The repaired title-derived pair uses canonical A4/27 mm/Libertinus styling and embeds PNG companions; three `pdflatex` passes produced a 34-page PDF with all fonts embedded/subset, no Type 3 font or overfull box, with all 18 current payload hashes verified. Its strict log-concavity, rootlessness, diffusion, and Legendre-jet strands remain paper-only and distinct, while scalar Stein-kernel, Bell-moment, shape, and endpoint material overlaps `Fabius_Stein_Koopman_Frontier_Report/`. The report now crosswalks the exact existing `rvachev_not_analyticAt` inputs separately from its prospective APIs and imports the stronger two-term endpoint theorem honestly. It remains standalone pending editorial integration; manuscript labels do not establish Lean status. The original 50-page Letter/Latin-Modern/Type-3 artifact is recoverable from history | arrived through `drafts/incoming/`; archive unpacked here and deleted |
| `Fabius_Stein_Koopman_Frontier_Report/` | *Dyadic Stein--Koopman and q-Oscillator Calculus for the Fabius--Rvachev Law* (32 pp, 1929 source lines; with exact-symbolic and numerical experiments, five generated data files, two dual-format figures, a corpus audit, build/preflight records, and reproducibility metadata). Landed 2026-08-30 from `drafts/incoming/Fabius_Stein_Koopman_Frontier_Report.zip`; all 20 payload checksums verified. The report develops Appell Koopman eigenmodes, finite and Fock-space transfer determinants, q-Weyl calculus, Poisson/Stein resolvents, martingales and nonreversibility, an exact scalar Stein kernel in Fabius coordinates, and Lambert-periodic endpoint asymptotics. It remains a separate representation member pending claim-by-claim Lean crosswalk and deliberate consolidation; theorem labels record paper proofs, not current Lean status | arrived through `drafts/incoming/`; archive unpacked here and deleted |
| `Representation_Frontiers/` | *Representation Frontiers for the Fabius–Rvachev System* (301 pp, 8 parts) — consolidation (2026-08-28) of all eight representation drafts. Parts I–III (first wave): `Fabius_Rvachev_Representation_Frontiers/` (*Fabius–Rvachev Representation Frontiers*: Jacobi coefficients, exact even moments, resolvent and logarithmic-derivative identities), `fabius_rvachev_representation_frontier/` (*Representation Atlas and New Analytic Bridges*), `Fabius_Rvachev_Multiresolution_Report/` (*Dyadic Multiresolution and Product–Series Representations*). Parts IV–VIII (second wave, folded in from the interim `Representation_Second_Wave/` volume on 2026-08-28): `fabius_rvachev_report_package/` (*Integral, Series, Product, and Operator Representations*), `Fabius_Rvachev_Polyphase_Representation_Report/` (*Polyphase, Operator, and Jump-Measure Representations*), `Fabius_Rvachev_Thue_Morse_Representation_Frontiers/` (*Sampling, Padé, Mellin, Resolvent, and Product–Integral Representations*), `rvachev_fabius_representations_2026/` (*Unit-Circle, Bessel, and Spectral–Monodromy Representations*), `Fabius_Rvachev_Multiresolution_Representations/` (*Dyadic Multiresolution and Sampling Frontiers*). The fold restored per-part arabic section numbering (the standalone second-wave volume let `\appendix` lettering run across part boundaries), restored the members' full part titles, and deduplicated colliding macros (all edits marked `% ed.:`); assets under `assets/`, provenance with SHA-256 in the document | absorbed drafts and the interim second-wave volume deleted; git history is the archive |
| `Up_Polynomial_Synthesis/` | *Exact Rvachev Up-Function Polynomial Synthesis* (60-page retained A4 PDF; 5,278 current source lines across a driver and three chapters; 80 theorem-like assertions, 80 proofs, and 80 one-to-one crosswalk rows: 25 + 16 + 17 + 22). Canonical editorial consolidation (2026-08-30) of three exact-polynomial, six Lagrange--Rvachev, and four Legendre--Rvachev packages, with repeated foundations deduplicated, exact Sturm evidence retained, and Lean anchors scoped claim by claim. The three earlier package payloads are under `assets/`; all 113 selected later-report payloads have canonical destinations and live hashes under `assets/companion-evidence/`, `assets/evidence/`, and `assets/provenance/COMPANION_PAYLOADS.csv`. The ten individual report directories were retired on 2026-08-31 after the exact gate passed; their source bytes remain recoverable at immutable commit `443793e846934e7363e314ea01129b9f50197a58`. | canonical volume; ten individual reports retired; current master plus three chapter sources are not yet recompiled; every current payload was hash-verified at that checkpoint, including the retained 60-page PDF as a historical artifact, and all evidence/provenance rows still verify |

Final post-union status for `Fabius_Rvachev_New_Frontiers-2/`: the row above
records the repaired package, whose filed TeX crosswalks the generic and
up-law determinant transports, executable rational Legendre coefficients and
Gram data, the exact low-order values leaf, and the generic/up-law finite Gaunt
modules.  The generic layer proves the
change-of-basis chain `G = Cᵀ H C`, upper-triangular `det C`, and the resulting
Gram/Hankel and Jacobi determinant ratios.  Its cross-ratio has no Hankel
nonvanishing premise only because division is total: a singular middle
determinant makes both sides zero, not a genuine nonsingular recurrence.  For
arbitrary `F : BoundedFabius`, the specialization proves the Legendre
determinant product, the empty-`0×0` convention `D_0 = 1`, the
leading-coefficient quotient, and the zero-based real Gram formula
`beta_(n+1) = ((n+1)/(2*n+1))^2 D_(n+2)D_n/D_(n+1)^2`.  Entry-as-integral,
strict positivity, rational casts, and the three real low-order transports
require `IsFabius F`; the rational leaf evaluates
`H_4 = 26727424/55791736875` and `beta_4 = 835232/4640643` exactly.  The new
Gaunt layer formalizes executable rational triple sums and their real-integral
casts, exact finite product linearization, parity/triangle-support zeros, and
finite up-law Gram-entry sums.  The downstream closed-form leaves define the
total integer-index zero-row square datum and prove its central-binomial and
factorial forms, all-degree Gaunt equality, sharp support/positivity, and finite
Wigner-square Gram sums.  Signed/general Wigner symbols and phase remain open,
as do Christoffel reconstruction, roots,
quadrature, Padé identification, infinite Jacobi products, and asymptotics;
`rvachevTranslateGram` is the separate unweighted shifted-up atom kernel.  Two
validated checkpoints remain historical evidence: the upstream 2,827-line,
39-page cleaned-vector build (35 embedded/subset font rows, five Libertinus,
no Type 3) and the local 2,864-line, 41-page Gaunt build (all 76 focused names,
including all 25 Gaunt names, and a then-verifying 20-entry ledger).  The
retained PDF's post-union source checkpoint was frozen at 2,863 lines with SHA-256
`4eeea1a1cbe5497e6db3424a0c185f3a3be750f5816b22be5e7baed091753455`.
That historical PDF has 41 A4 pages, 780,141 bytes, and SHA-256
`9871ac93cce5d8ee1aa48e946f46dc2e19865fb33a1d2e3b9b8be01360318901`.
Its strict 39/41/41-page build, font/extraction gates, visual review, and
preflight all passed at that checkpoint.  The current 2,978-line,
122,235-byte source has SHA-256
`e0015e424fe577c4aee3ea473ace71b67b9f250d5a96569dccd6dd03ebe20c98`;
it and the mixed 20-payload hash audit are newer.  No rebuilt PDF is claimed,
and the two still older PDFs are historical only.

The CRLF/LF mismatch descriptions in the three rows above record the landing
state.  Their payload hashes were subsequently rechecked against the
repository-normalized LF bytes, so all three complete payload checks passed;
the original arrival bytes remain recoverable from git history.

## frontier-compilations — `frontier-compilations/`

Broad multi-topic "collected new results" reports, kept together as a
series even where a single title leans toward another group.

| Directory | Document | Previous path |
| --- | --- | --- |
| `Geometric_Uniform_Frontier_Directions/` | *Frontier Directions for Geometric-Uniform and Fabius--Rvachev Analysis* (30 A4 pp, 1,641-line TeX; with an 874-line reproducible experiment, ten CSV/text data products, eight dual-format figures, a hostile corpus audit, and validation records). Filed 2026-08-30 from `fabius_frontier_report_bundle-D.zip` (1,508,514 bytes; SHA-256 `39f3638f52f19955b88b7a865a60b76d9ce31154d98967d1400a6ad97396fa9a`); all 34 arrival payload hashes and all 36 current payload hashes verified. Exact tables replayed; floating outputs agree within the documented last-place/platform tolerances. The corpus crosswalk distinguishes existing geometric-uniform, q-moment, and Fabius infrastructure from the paper-level asymptotic, large-deviation, Edgeworth, zero-count, and periodic claims. The canonical A4/27 mm/Libertinus report and all vector figures contain no Type 3 fonts and were rebuilt in exactly three strict passes | arrived through `drafts/incoming/`; archive unpacked here and deleted |
| `Geometric_Uniform_Convolutions_and_New_Frontiers/` | *Geometric Uniform Convolutions and New Frontiers around the Fabius--Rvachev System* (1,656 source lines), delivered as one LF TeX source under the generic wrapper `fabius-frontier-report-H/` in direct-arrival commit `8a184546747082cbd92ad4675fb61981c6b8c3b6`. No PDF, README, code, data, figures, output, archive, metadata, or hash manifest was supplied. Intake repaired three form-feed-corrupted `\frac` tokens and recorded the source fingerprint directly. Its abstract says Python code accompanies the report, but none is present. Its broad q/Edgeworth, Thue--Morse, Bell--Bernoulli, valuation-zero, Fourier-zero, derivative-growth, non-Gevrey, and Lambert strands remain standalone pending compilation, claim comparison, and a Lean crosswalk; the package still has no PDF, the source has not yet been shown to compile, and manuscript labels do not establish Lean verification | `drafts/incoming/fabius-frontier-report-H/`; renamed and filed here |
| `Frontier_Compilations/` | *Collected Frontier Reports for the Fabius–Rvachev System* (retained 274-page PDF; current source not recompiled; ten absorbed reports; ten rendered parts) — consolidation (2026-08-28) of the former `Fabius_Rvachev_Frontier_Report/`, `-2/`, `-3/`, `Fabius_Rvachev_Frontier_Report_2026-08-27/`, `Fabius_Rvachev_New_Frontiers/`, `fabius_frontier_report_bundle/`, `fabius_frontier_results_bundle/`, `fabius_frontier_new_results/`, `fabius_frontier_spectral_endpoint_report_bundle/`, and `beyond_dyadic_fabius_web_report/` (source reports I–X render one-to-one as Parts I–X; former titles in the group README); assets under `assets/`, provenance with SHA-256 in the document | absorbed drafts deleted; git history is the archive |
