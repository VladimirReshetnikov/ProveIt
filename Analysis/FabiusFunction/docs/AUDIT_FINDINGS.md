# Audit findings

Surviving results of a read-only audit of every module in
`Analysis/FabiusFunction/Lean`.  Eleven cluster auditors read the whole corpus;
every candidate finding was then handed to a separate agent whose instructions
were to *refute* it, defaulting to refuted when it could not positively confirm
the claim.  Of 121 candidates, 103 survived and 18 were killed.

**Nothing here is a build result.**  A surviving finding means an independent
reader checked the cited declarations, the boundary cases, and the proposed
replacement against the source and could not refute it.  It does not mean the
proposed edit has been compiled.  Treat each entry as a reviewed proposal, not
as a patch.

Long proposals and verifier notes are abridged.  When an entry matters, re-read
the cited source rather than trusting the abridgement.

## How to use this file

Take one entry, re-read the cited source, and either implement it or strike it
with a reason.  Do not batch unrelated entries into one commit unless they share
a blast radius: several touch modules with more than a hundred downstream
consumers, and the only reason to group them is to pay that invalidation once.

When an entry is closed, mark it DONE in place rather than deleting it.  The
record of what was considered and rejected is worth as much as the record of
what was done -- this audit exists partly because the same abstractions were
independently rediscovered three times by three branches.

A caution on the hypothesis-weakening entries: removing a hypothesis changes a
theorem's arity, which is API.  Per `COLLABORATION.md`, either fix every call
site in the same commit or keep the old signature as a compatibility wrapper.

## A defect taxonomy for reviewers

Three defect classes turned up repeatedly while this audit and the two
documentation passes ran.  None of them is caught by the compiler, and the
first two are not caught by any check that only reads statements.  A reviewer
who knows to look for them finds them cheaply; one who does not will not find
them at all.

### 1. False universal

Prose that asserts more than the surrounding development supports, almost
always about *dependencies* rather than about mathematics.  "Every coefficient
computation below factors through this" when one does not.  "The denominator in
every ratio bound here" when it is the denominator of one.  "Used by `X`" when
`X` re-derives it inline.

This was by far the most common defect, in both documentation waves.  The
reason it is common is structural: a claim about a statement can be checked
against the statement on the next line, and a claim about a dependency cannot
be checked without grepping the corpus, so it is the claim an author is most
tempted to write from memory.

*Detection.* Grep every "used by", "every", "only", "all" in a doc comment.
*Prevention.* Write no consumer clause you have not grepped.  A doc comment
with no dependency claim is fine; one with a false claim is a defect.

An author is not exempt from this.  One entry in this corpus documented
`fabiusInv_half` as "the only interior value known in closed form", which this
very corpus refutes: `DyadicAnalytic.fabiusDyadicUnit_cast` evaluates `F`
exactly at every dyadic rational, and `F(1/4) = 5/72` is the threshold the
same module's own theorem uses.

### 2. Vacuous specialization

A theorem that is true, compiles, and whose hypothesis almost nothing can
satisfy.  This is worse than a false theorem, because a false theorem breaks
something downstream and a vacuous one never will.

The case that produced this entry: a leading-coefficient law stated as a
difference between two evaluation points `t` and `u` at which the first
`2j + 1` jets agree.  The jets are one-periodic, so `u = t + 1` satisfies the
hypothesis and yields `0 = 0`; for `u` not congruent to `t` the hypothesis
holds only on a measure-zero set.  The generic statement over an arbitrary jet
sequence was sound throughout — only the specialization to Fabius was
degenerate, which is what made it hard to see.

*Detection, from the signature alone.*  A theorem quantified over a **free
parameter** is hard to make vacuous: witnesses are trivial to produce and
manifestly disagree.  A theorem quantified over **two constrained instances of
a fixed object** is easy to make vacuous, because the constraint may admit only
the trivial pair.  That is the whole difference between the generic and
specialized forms in the case above, and it is readable off the binders before
any thought about the mathematics.  Check that first; it costs seconds.

*Detection, when the signature does not settle it.*  For every hypothesis, ask
**who can satisfy it**, and produce two genuinely different witnesses.  If the
only witnesses you can construct make both sides of the conclusion equal, the
theorem is vacuous at exactly the points you care about.  Periodicity, symmetry
and reflection hypotheses are the usual sources, because they silently supply a
trivial witness — and in this repository nearly every object in the asymptotic
layer is one-periodic, so the trivial witness is always available.
*Prevention.* Prefer a statement that *exhibits* a dependence — an affine
decomposition, an explicit formula — over one that asserts it as an equality
between two points constrained to agree.

### 3. Sharpness and smoothness overclaim

Writing "sharp", "optimal", "exact" or "if and only if" over a one-directional
bound whose converse the file does not prove; or writing "valid only for" about
an interval that is merely the one the statement mentions, when the file proves
no converse and the bound in fact holds outside it.

In this corpus the smoothness variant has a specific trap.  `ContDiff R (top)`
at type `WithTop ENat` is the *analytic* exponent, and `ContDiff R infinity` is
`C^infinity`; the two look alike and mean different things.  The corpus's
central regularity theorem is that the Fabius function is `C^infinity`
everywhere and analytic exactly off `[0,1]`, so this is the one confusion the
library exists to prevent, and two doc comments had it backwards.

*Detection.* Every occurrence of sharp / optimal / exact / iff / only, and
every occurrence of smooth / analytic, checked against the statement it sits
above.

## Status

Entries closed so far, with the commit that closed them.  Marked DONE in place
below rather than deleted.

| Entry | Commit | Compiled |
| --- | --- | --- |
| The triangular identity `(n+1).choose 2 = n.choose 2 + n`, ten private copies (reported independently by five of the eleven auditors) | `1ea3554f4` | `Arithmetic` green, 1053 jobs, exit 0.  The eighteen rewired call sites are downstream and not yet exercised. |
| `thueMorseSign_block_concat` and the two range block-decomposition lemmas, triplicated across three modules | `affa557d2` | not yet |
| The four `negativeLaplaceLog*_two_mul` and three `negativeLaplaceVerticalLog*_two_mul` proofs, consolidated into `ScalingRecurrence` | `affa557d2` | `ScalingRecurrence` green, 1984 jobs, exit 0 |
| The repeated Legendre hypothesis bundle, four copies | `4a1639106` | not yet |
| Missing module headers on twelve modules, stub headers on five | `4c59369fe` | comment-only |
| Undocumented public declarations: 862 to 176 | `35d14fe40`, `9827b5485`, `ae6176d6e` | comment-only |
| `expCoeff` values missing from the generic saddle algebra | asymptotic-expansion branch | `FabiusSaddleJetClosedForm` green |

Two builds have run, both on a peer's build slot at the SHAs named above, in a
sparse detached worktree whose `.lake/packages` is a junction to the shared
Mathlib.  That technique lets one agent validate another's commit without
either of them merging, and is why these two lines exist at all: this branch
has started no Lean process.

## Summary

| Kind | Count |
| --- | --- |
| Hypothesis weakening | 28 |
| Missing corollaries | 10 |
| Deduplication | 44 |
| Private declarations worth exposing | 9 |
| Proof shortening | 5 |
| Documentation | 7 |
| **Total** | **103** |

By cluster: core 7, discrete-limits-computability 10, dyadic 8, fourier-legendre 9, lambert-asymptotics 12, moments-probability 12, negative-laplace 6, papers-aggregates 11, regularity 10, saddle 10, thuemorse-qbinomial 8.

## Hypothesis weakening

### Cluster: core

#### IMPLEMENTED: `IsOriginalFabius.scale_pos` is a redundant structure field: positivity of the dilation constant follows from the other five hypotheses

Confidence medium.  `OriginalCharacterization.lean`, `OriginalUniqueness.lean`

**Why.** Before this strengthening, `scale_pos` was supplied only by callers and
was not consumed by the proof of `IsOriginalFabius.scale_eq_two`.  That proof
uses only `hasDerivAt`, support consequences, `contDiff`, `value_zero`, and the
normalization argument.  The smart constructor now records the derived
positivity in the retained compatibility field.

**Implementation.** CONFIRMED with two corrections.  The compatibility-preserving
smart constructor is now `IsOriginalFabius.mk_of_derivative_law`; the
source-faithful `scale_pos` field remains in the structure.

Correct core claim: `scale_pos : 0 < k` is a redundant field of
`IsOriginalFabius`; it follows from `contDiff`, `tsupport_eq`, `pos_of_mem`,
`value_zero`, and `hasDerivAt`.  The implemented declaration is:

theorem IsOriginalFabius.mk_of_derivative_law {φ : ℝ → ℝ} {k : ℝ}
    (hcontDiff : ContDiff ℝ ∞ φ)
    (htsupport : tsupport φ = Set.Icc (-1 : ℝ) 1)
    (hpos : ∀ x ∈ Set.Ioo (-1 : ℝ) 1, 0 < φ x)
    (hvalue : φ 0 = 1)
    (hderiv : ∀ x : ℝ, HasDerivAt φ (k * (φ (2 * x + 1) - φ (2 * x - 1))) x) :
    IsOriginalFabius φ k

CORRECTION 1 (proof route). Route (b) is not needed and route (a) is far cheaper than the finding states. The refactor does NOT touch lines 62-231 and does NOT require restating `intervalIntegral_eq_one` or "four upstream lemmas". Only two facts must be reproved standalone, ~15 lines total, and both are one-liners from `htsupport`/`hcontDiff`:
  - `hfar : ∀ x, x < -1 → φ x = 0` (directly from `htsupport` via `subset_tsupport`; note `2*c - 1 < -1` strictly, so `value_neg_one` is NOT needed here);
  - ...

**Verifier.** The finding survived adversarial checking before implementation:
the mean-value point lies strictly in `(-1,0)`, so one translated argument is
strictly outside the support and the other is strictly inside it.  Thus the
proof never assumes endpoint positivity, and `k ≤ 0` is impossible.

#### `card_odd_inner_binomial_coefficients` does not need `1 ≤ m`

Confidence high.  `Parity.lean:196`, `Parity.lean:179`

**Why.** The companion theorem two declarations above (`odd_binomial_coefficient_counts`, line 179) carries the docstring "The result is valid also at `n = 0`, so no positivity hypothesis is needed here" — the author deliberately hunts for exactly this. The hypothesis on line 196 was evidently kept because the `2 ^ w - 3` shape looks dangerous at `m = 0`, but truncated subtraction makes it come out right.

**Proposal.** Add the all-index form next to it, exactly as the file already does for `odd_binomial_coefficient_counts` and as TwoAdic.lean does for `two_mul_halfMoment_recurrence_all` / `two_mul_halfMoment_recurrence`:

```
/-- All-index form of the inner odd-coefficient count.  At `m = 0` both sides
are zero, the right-hand side by truncated natural subtraction. -/
theorem card_odd_inner_binomial_coefficients_all (m : ℕ) :
    ((range (2 * m)).filter (fun k =>
      k ≠ 0 ∧ Odd (Nat.choose (2 * m + 1) k))).card =
        2 ^ (binaryWeight m + 1) - 3 := by
  cases m with
  | zero => decide
  | succ m => exact card_odd_inner_binomial_coefficients (m + 1) (by omega)
```

and keep `card_odd_inner_binomial_coefficients` unchanged as the compatibility wrapper. Home module: Parity.lean.

**Verifier.** Survives every check. (1) Signature quoted verbatim correctly: Parity.lean:196 is `card_odd_inner_binomial_coefficients (m : ℕ) (hm : 1 ≤ m)` with RHS `2 ^ (binaryWeight m + 1) - 3`, and Parity.lean:179 `odd_binomial_coefficient_counts` really does carry the docstring "The result is valid also at `n = 0`, so no positivity hypothesis is needed ...

### Cluster: discrete-limits-computability

#### `fabiusUniformSpline_mem_Icc` does not need `0 < p`, and the degree-zero argument is already written out inline in a downstream module

Confidence high.  `FabiusUniformSpline.lean:1042`, `FabiusUniformSpline.lean:1052`, `FabiusUniformSpline.lean:1199`, `FabiusComputability.lean:99`, `FabiusComputableSpline.lean:417`

**Why.** The `0 < p` hypothesis is an artifact of routing through `fabiusUniformSpline_eq_centeredPartialCDF`, which needs positive degree. But the degree-zero case is separately proved 157 lines further down in the same file as `fabiusUniformSpline_zero_eq_centeredPartialCDF_of_mem_Icc` (line 1199), so nothing is missing. The consequence is visible twice downstream: FabiusComputability.lean:104–112 hand-writes the `p = 0` branch (`rw […fabiusUniformSpline_zero_eq_centeredPartialCDF_of_mem_Icc hx]; ...

**Proposal.** In `namespace ProbabilityRepresentation` of FabiusUniformSpline.lean, immediately after `fabiusUniformSpline_zero_eq_centeredPartialCDF_of_mem_Icc` (currently line 1158) and next to `monotoneOn_fabiusUniformSpline_all` (currently line 1178), add the all-degree companion, leaving the positive-degree `fabiusUniformSpline_mem_Icc` (currently line 1001) in place exactly as the file already leaves `monotoneOn_fabiusUniformSpline` in place:

/-- Centered finite splines take values in `[0,1]` on the fundamental interval in every
degree, including the degree-zero step spline. -/
theorem fabiusUniformSpline_mem_Icc_all (p : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    fabiusUniformSpline p x ∈ Icc (0 : ℝ) 1 := by
  cases p with
  | zero =>
      rw [fabiusUniformSpline_zero_eq_centeredPartialCDF_of_mem_Icc hx]
      exact ⟨ProbabilityTheory.cdf_nonneg _ _, ProbabilityTheory.cdf_le_one _ _⟩
  | succ p => exact fabiusUniformSpline_mem_Icc (p + 1) (by omega) hx

(The zero branch is the argument already written out at FabiusComputability.lean:106-108; if the anonymous constructor does not unify ...

**Verifier.** Survives verification, with corrections. (1) Every cited declaration exists with the exact quoted signature, though line numbers drifted ~41 lines because the worktree HEAD advanced during checking (768357067 -> affa557d2): fabiusUniformSpline_mem_Icc is now FabiusUniformSpline.lean:1001, abs_fabiusUniformSpline_le_one_of_mem_Icc :1011, ...

#### The complex-shift translation bounds carry `1 ≤ p` (and one carries `0 ≤ x`) that the statements do not need

Confidence high.  `FabiusDiscreteLimitComplexShift.lean:284`, `FabiusDiscreteLimitComplexShift.lean:207`, `FabiusComplexShiftSpline.lean:205`, `FabiusComplexShiftSpline.lean:238`, `FabiusComplexShiftSpline.lean:44`

**Why.** At `p = 0` the degree-zero branch `normalizedThueMorseSplineBranch 0 M z = (∑ r ∈ range M, thueMorseSign r) / 1` does not depend on `z` at all, so the left-hand side is exactly `0`; and by ℕ-truncated subtraction the right-hand side is `(1/2)^0 * Real.exp ‖δ‖ = Real.exp ‖δ‖ ≥ 0`. The bound therefore holds trivially in the excluded degree, and the same is true of the spline version. Separately, on `x ≤ 0` both `fabiusComplexShiftSpline p q x` and `fabiusComplexShiftSpline p (1/2) x` are exactly ...

**Proposal.** Add three unconditional companions and keep the current names as wrappers.

1. FabiusDiscreteLimitComplexShift.lean, after line 317:

theorem norm_normalizedThueMorseSplineBranch_add_sub_le_half_pow_mul_exp_all
    (p M : ℕ) (z δ : ℂ)
    (hbound : ∀ d ∈ Finset.range p, ‖normalizedThueMorseSplineBranch d M z‖ ≤ 1) :
    ‖normalizedThueMorseSplineBranch p M (z + δ) - normalizedThueMorseSplineBranch p M z‖ ≤
      (1 / 2 : ℝ) ^ (p - 1) * Real.exp ‖δ‖

Proof: `rcases Nat.eq_zero_or_pos p with rfl | hp`; positive case is the existing theorem applied with `hp`; zero case is `le_trans (norm_normalizedThueMorseSplineBranch_add_sub_le 0 M z δ hbound) h` where `h` is discharged by first reducing the empty `Finset.range 0` sum (e.g. `by simp; positivity`, or `by norm_num [Real.exp_nonneg]`) — NOT by `positivity` alone, which does not take a `≤` goal.

2. FabiusComplexShiftSpline.lean: also weaken the intermediate `norm_fabiusComplexShiftSpline_sub_center_le_half_pow_mul_exp_of_bound` (line 142) by dropping its `hp : 1 ≤ p` — its proof passes `hp` straight into the branch bound at line 161, so ...

**Verifier.** All cited declarations exist with the quoted signatures (line 284, line 207, line 238 exactly; `fabiusComplexShiftSpline_eq_zero_of_nonpos` at 45 not 44; `norm_normalizedThueMorseSplineBranch_add_sub_le` at 179 not 178 — offsets only, no math misquoted). The boundary case is genuinely harmless: at `p = 0`, `normalizedThueMorseSplineBranch 0 M w = ...

#### The complex-MGF derivative bound is stated only on the parametrized line `-(r(1+θi))`, but its proof gives it at every point of ℂ

Confidence high.  `FabiusComplexMGF.lean:97`, `FabiusComplexMGF.lean:85`, `EndpointLaplaceComparison.lean:645`, `LaplaceMoments.lean:112`

**Why.** The vertical-line parametrization `z = -(r(1+θi))` is a fixed cutoff that never enters the argument. The proof bounds `‖x^n * Complex.exp (z*x)‖` by `Real.exp ((z*x).re) * x^n = Real.exp (z.re * x) * x^n`, so the only feature of `z` used is its real part. Since `fabiusLaplaceMoment F n s` (LaplaceMoments.lean:112) and `unitLaplaceMoment μ s k` (EndpointLaplaceComparison.lean:233) are both defined for every real `s`, and `unitLaplaceMoment_weightedSumDistribution_eq_fabiusLaplaceMoment F hF k s` ...

**Proposal.** Add to FabiusComplexMGF.lean, immediately before the existing theorem:

  /-- The norm of every complex derivative of the generating function is bounded by the real
  tilted moment at the abscissa of the evaluation point. -/
  theorem norm_iteratedDeriv_complexGeneratingFunction_le
      (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (z : ℂ) :
      ‖iteratedDeriv n (complexGeneratingFunction F) z‖ ≤
        fabiusLaplaceMoment F n (-z.re)

and keep the existing name as a compatibility wrapper:

  theorem norm_iteratedDeriv_complexGeneratingFunction_neg_vertical_le
      (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (r θ : ℝ) : … :=
    by simpa using norm_iteratedDeriv_complexGeneratingFunction_le F hF n
         (-((r : ℂ) * (1 + (θ : ℂ) * Complex.I)))

**Verifier.** The finding survives adversarial checking on every axis.

(1) Signatures are quoted accurately. FabiusComplexMGF.lean:97-101 matches the `current` text verbatim, with no sign hypothesis on `r` or `θ`. `unitLaplaceMoment` is at EndpointLaplaceComparison.lean:233 with argument order `(μ) (s) (k)` exactly as described; ...

#### Three shift specializations keep `0 ≤ x` although the general theorem they wrap holds on all of ℝ

Confidence high.  `FabiusComplexShiftSpline.lean:344`, `FabiusComplexShiftSpline.lean:351`, `FabiusComplexShiftSpline.lean:358`, `FabiusComplexShiftSpline.lean:305`

**Why.** `fabiusComplexShiftSpline_tendsto_globalFabius_all` (line 305) already removes the nonnegativity restriction from the master theorem, and the sibling module FabiusDiscreteLimitIntegration.lean systematically provides `_all` forms for exactly this reason (`…Rat_tendsto_globalFabius_all`, `…GaussianRat_tendsto_globalFabius_all`, `…Real_tendsto_globalFabius_all`). The three specializations here were left wired to the restricted version, so the shift-specialized API is strictly weaker than both the ...

**Proposal.** Correction to the citation only: the general theorem `fabiusComplexShiftSpline_tendsto_globalFabius_all` is declared at FabiusComplexShiftSpline.lean:294 (50 lines above line 344), not line 305 — line 305 is the `simpa [hspline, hglobal] using` step inside its proof. The substance is unchanged. Add these three declarations after line 364, keeping the existing restricted forms untouched as the `0 ≤ x` API, exactly mirroring the restricted/`_all` pairing already used at lines 311/323 of this module and throughout FabiusDiscreteLimitIntegration.lean:

/-- Arbitrary real shifts converge on the whole real line. -/
theorem fabiusComplexShiftSpline_tendsto_globalFabius_real_all (q x : ℝ) :
    Tendsto (fun p : ℕ => fabiusComplexShiftSpline p (q : ℂ) x)
      atTop (nhds (globalFabius x : ℂ)) :=
  fabiusComplexShiftSpline_tendsto_globalFabius_all (q : ℂ) x

/-- Rational shifts converge on the whole real line. -/
theorem fabiusComplexShiftSpline_tendsto_globalFabius_rat_all (q : ℚ) (x : ℝ) :
    Tendsto (fun p : ℕ => fabiusComplexShiftSpline p (q : ℂ) x)
      atTop (nhds (globalFabius x : ...

**Verifier.** The finding survives adversarial checking on every axis. (1) Signatures verified verbatim: FabiusComplexShiftSpline.lean:344/351/358 carry `{x : ℝ} (hx : 0 ≤ x)` and are pure one-line wrappers over the restricted `fabiusComplexShiftSpline_tendsto_globalFabius`. (2) The general theorem `fabiusComplexShiftSpline_tendsto_globalFabius_all (q : ℂ) (x : ...

### Cluster: dyadic

#### The `_of_kernel` family carries a hypothesis that is discharged 157 lines earlier in the same file

Confidence high.  `DyadicClosedForm.lean:728`, `DyadicClosedForm.lean:734`, `DyadicClosedForm.lean:891`, `DyadicClosedForm.lean:930`, `DyadicClosedForm.lean:939`

**Why.** `DyadicKernelHasRefinement` is not an open conjecture threaded through the development the way `FabiusDyadicHasBitRecurrence` is (that one really is discharged in a downstream module). It is proved unconditionally by `dyadicKernel_has_refinement` at line 734, i.e. *before* every one of its four consumers in the same file. Every caller inside and outside the module therefore just writes `... dyadicKernel_has_refinement ...`; `dyadicBlock_eq_taylor_sum` (line 958, the one that is actually ...

**Proposal.** Add ONE hypothesis-free theorem in DyadicClosedForm.lean, immediately after `fabiusDyadic_refine_of_kernel` (currently line 913, was 891), and update the two external call sites. Keep `fabiusDyadic_refine_of_kernel` as-is, since it is still applied with an explicit `hk` inside the module at line 959.

/-- Doubling both the exponent and the numerator leaves equation (32) unchanged. -/
theorem fabiusDyadic_refine (n a : ℕ) :
    fabiusDyadic (n + 1) (2 * a) = fabiusDyadic n a :=
  fabiusDyadic_refine_of_kernel dyadicKernel_has_refinement n a

Then `DyadicAnalytic.lean:283` becomes `have hrefine := fabiusDyadic_refine n 1` and `FabiusQBinomialFormula.lean:1490` (NOT 1529 — that file is now 1511 lines after commit affa557d2) becomes `exact fabiusDyadic_refine n m`.

Do NOT add hypothesis-free versions of `fabiusDyadic_refine_pow_of_kernel`, `fabiusDyadic_pow_two_eq_inverse_of_kernel`, or `dyadic_block_base_eq_inverse_of_kernel`. Each has exactly one caller, all inside DyadicClosedForm.lean (lines 959, 978, 994), and in every case `hk` is already bound or `dyadicKernel_has_refinement` is ...

**Verifier.** The finding survives verification. Every cited line is exact against the session-start HEAD (768357067): DyadicKernelHasRefinement at DyadicClosedForm.lean:728, dyadicKernel_has_refinement at :734, and the four _of_kernel lemmas at :891/:930/:939/:945, with the quoted signatures matching the source character-for-character. The gap of 157 lines is ...

#### Six half-moment/log bounds needlessly assume `1 ≤ n`, and four of them have `F`-free conclusions

Confidence high.  `FabiusDyadicLogBounds.lean:53`, `FabiusDyadicLogBounds.lean:82`, `FabiusDyadicLogBounds.lean:128`, `FabiusDyadicLogBounds.lean:135`, `FabiusDyadicLogBounds.lean:191`

**Why.** Four of the six conclusions mention neither `F` nor `hF` — they are statements about the purely rational sequence `halfMoment : ℕ → ℚ` that currently cannot be used without producing a `BoundedFabius` witness. And in every one of the six the `n = 0` case is true and trivial (`halfMoment 0 = 1` by Arithmetic.lean:276, `fabiusReal F 1 = 1`, and `dyadicLogError F 0 = 0` with both bounds equal to `0`). The doc comments already promise the stronger statements: "The half moments are at most one", "A ...

**Proposal.** Add six unrestricted forms to FabiusDyadicLogBounds.lean and demote the existing six to thin wrappers.

New statements (home module FabiusDyadicLogBounds.lean, which already imports PaperStatements):

  theorem halfMoment_le_one (n : ℕ) : halfMoment n ≤ 1
  theorem inv_two_pow_succ_le_halfMoment (n : ℕ) : ((2 : ℚ) ^ (n + 1))⁻¹ ≤ halfMoment n
  theorem log_halfMoment_nonpos (n : ℕ) : Real.log (halfMoment n : ℝ) ≤ 0
  theorem neg_succ_mul_log_two_le_log_halfMoment' (n : ℕ) :
      -((n + 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (halfMoment n : ℝ)
  theorem dyadicLogError_bounds_all (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
      -3 * (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) ≤ dyadicLogError F n ∧
        dyadicLogError F n ≤ 3 * (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)
  theorem abs_dyadicLogError_le_all (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
      |Real.log (fabiusReal F (((2 : ℝ) ^ n)⁻¹)) + Real.log 2 / 2 * (n : ℝ) ^ 2| ≤
        3 * (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)

Proof route, as stated in the finding: `cases n`; the `zero` branch closes by `simp [halfMoment_zero]` / ...

**Verifier.** All eight cited locations exist with the signatures as quoted, and the boundary case is safe. halfMoment_zero (Arithmetic.lean:276) gives halfMoment 0 = 1, so at n = 0 the four half-moment claims reduce to 1 ≤ 1, 1/2 ≤ 1, log 1 = 0 ≤ 0, and -log 2 ≤ 0 — all true. For the two F-carrying claims, dyadicLogError_eq (FabiusDyadicLogBounds.lean:168) ...

#### IMPLEMENTED: the signed-global inverse-dyadic recurrence is generic in `(F, hF)`

Confidence high.  `FabiusRecurrenceSequence.lean`,
`FabiusInverseDyadicClosedForm.lean`

**Why.** The bounded inverse-dyadic recurrence already came in generic and
canonical forms, and the signed extension agrees with the bounded function at
every inverse-dyadic argument in `[0,1]`.  The previous canonical-only global
proof therefore contained no canonical ingredient beyond its final
specialization.

**Implementation.** `extendedFabius_inverse_two_pow_recurrence` now states the
literal `2^(-n)` recurrence for every `F : BoundedFabius` satisfying
`IsFabius F`.  It rewrites each inverse-dyadic signed value with
`extendedFabius_eq_fabiusReal` and delegates to the existing generic bounded
recurrence.  `globalFabius_inverse_two_pow_recurrence` is retained unchanged as
a two-line specialization to `fabius` and `fabius_spec`.  The necessary
hypothesis `1 ≤ n` remains: at `n = 0` the displayed denominator vanishes while
the normalized value at `1` is one.

### Cluster: fourier-legendre

#### The hypothesis a ≤ 1 is unused in both Poisson support-specialization theorems

Confidence high.  `PoissonSummation.lean:451`, `PoissonSummation.lean:465`

**Why.** The upper bound `a ≤ 1` is transcribed from the paper but plays no role: the author already wrote it as `_ha1`, i.e. Lean's own convention for a binder that is never used. The scaled theorem passes `ha1` down solely to feed that dead binder, so it too is superfluous. Every ingredient — `rvachev_poisson_at_zero` (needs `0 < a`, derived from `ha0`) and `rvachev_lattice_sum_of_one_half_le` (PoissonSummation.lean:~415, needs only `1/2 ≤ a`) — is already stated for all `a ≥ 1/2`. The stronger form ...

**Proposal.** Title should read: "The hypothesis `a <= 1` is dead weight in both Poisson support-specialization theorems" — in `rvachev_poisson_support_specialization_unscaled` the binder is literally unused (`_ha1`), while in `rvachev_poisson_support_specialization` `ha1` is used only at line 471 to feed that dead binder, so it is vacuous rather than unused. Also correct the citation for `rvachev_lattice_sum_of_one_half_le` from "~415" to PoissonSummation.lean:424 (415 is `rvachev_poisson_at_zero`).

The code proposal itself is correct as written and matches the project's own rule at docs/COLLABORATION.md:192-193. Add, in PoissonSummation.lean immediately before the existing declarations:

/-- Equation (32) holds for every lattice spacing `a >= 1/2`, not only for `a <= 1`. -/
theorem rvachev_poisson_support_specialization_unscaled_of_one_half_le
    (F : BoundedFabius) (hF : IsFabius F) {a : ℝ} (ha0 : 1 / 2 ≤ a) :
    (1 : ℂ) + 2 * rvachevUp F a =
      ∑' m : ℤ, ((a⁻¹ : ℝ) : ℂ) * rvachevFourier F ((((m : ℝ) / a : ℝ) : ℂ))

theorem rvachev_poisson_support_specialization_of_one_half_le
    (F : ...

**Verifier.** The finding survives adversarial checking. Signatures at PoissonSummation.lean:451-457 and 465-470 are quoted verbatim, `_ha1` included. Every ingredient is already stated without an upper bound on `a`: `rvachev_poisson_summation` (line 86) and `rvachev_poisson_at_zero` (line 415) require only `0 < u` / `0 < a`, and ...

### Cluster: lambert-asymptotics

#### `smallArgumentLog_inv_eq` needs no hypothesis at all; the resulting Big-O comparison holds on every filter, killing a duplicated proof block

Confidence high.  `FabiusLambertRates.lean:43`, `FabiusLambertRates.lean:67`, `FabiusWikipediaExpansion.lean:267`, `FabiusLambertAllOrderSmallArgument.lean:108`, `FabiusSmallArgumentScale.lean:19`

**Why.** `fabiusSmallArgumentLog x = -Real.logb 2 x` and `Real.logb b x = Real.log x / Real.log b` by definition, so both sides are `((-Real.log x) * (Real.log 2)⁻¹)⁻¹` versus `Real.log 2 * (-Real.log x)⁻¹`. In ℝ inversion is total (`0⁻¹ = 0`), so `mul_inv_rev` + `inv_inv` prove the identity for every real `x` — including `x = 0`, `x = 1`, and `x < 0`. The `0 < x` hypothesis and the `by_cases h : x = 1` branch are pure artifacts of proving it with `field_simp`. Because the identity is filter-free, the ...

**Proposal.** The finding stands as stated; two cosmetic corrections to the proposal text.

(a) The suggested compatibility wrapper `fun hx => smallArgumentLog_inv_eq' _` does not typecheck, since `hx` is already bound by the theorem signature, and an unused `hx` binder trips the `unusedVariables` linter. If a wrapper is kept it must read:

theorem smallArgumentLog_inv_eq {x : ℝ} (_hx : 0 < x) :
    (fabiusSmallArgumentLog x)⁻¹ = Real.log 2 * (-Real.log x)⁻¹ :=
  smallArgumentLog_inv_eq' x

(b) The wrapper is not actually needed. `smallArgumentLog_inv_eq` has exactly three references in the whole corpus — FabiusLambertRates.lean:71, FabiusWikipediaExpansion.lean:271, FabiusLambertAllOrderSmallArgument.lean:108 — all passing `hx` positionally, and no doc file under Analysis/FabiusFunction mentions the name. So the cleaner edit is to weaken `smallArgumentLog_inv_eq` in place to `(x : ℝ)` with the six-rewrite proof, add `smallArgumentLog_inv_isBigO` beside it (or in FabiusSmallArgumentScale.lean as proposed), replace the two `htarget` blocks with `smallArgumentLog_inv_isBigO _`, and change line ...

**Verifier.** Confirmed on every axis. (1) Signature at FabiusLambertRates.lean:43-52 matches the quote verbatim. (2) The weakened statement is TRUE at every boundary: with Real.log 0 = 0, Real.log 1 = 0, and 0⁻¹ = 0 in ℝ, both sides are 0 at x = 0, x = 1, and x = -1; for x < 0 with log|x| ≠ 0 (e.g. x = -2) both sides equal -1; for log x ≠ 0 both sides equal ...

#### `rvachevUp_eq_one_sub_fabiusReal_of_mem_Icc` only needs `0 ≤ t`, and belongs next to `IsFabius.symmetry_all`, which already does the work

Confidence high.  `LaplaceTransform.lean:35`, `GlobalDyadic.lean:39`, `Basic.lean:77`, `EndpointLaplaceComparison.lean:545`

**Why.** `IsFabius.symmetry_all` (Basic.lean:77) already extends the reflection identity `fabiusReal F (1 - x) = 1 - fabiusReal F x` from `Icc 0 1` to all of ℝ, so for `0 < t` the identity `rvachevUp F t = fabiusReal F (1 - t) = 1 - fabiusReal F t` needs no upper bound; `rvachevUp_of_pos` (Basic.lean:112) does the unfolding. The author instead used `hF.symmetry t ht`, which forces the `Icc` hypothesis. `0 ≤ t` is sharp: at `t = -1/2`, `rvachevUp F (-1/2) = fabiusReal F (1/2) = 1/2 ≠ 1 = 1 - fabiusReal F ...

**Proposal.** Weaken the hypothesis to `0 ≤ t` as proposed, but land it on top of the existing `0 ≤ x` unfolding lemma instead of re-deriving that split a third time.

Step 1. Move `rvachevUp_eq_fabiusReal_one_sub` from Monotonicity.lean:283 to Basic.lean, immediately after `rvachevUp_zero` (Basic.lean:147). Its proof uses only `rvachevUp_of_nonpos` (Basic.lean:107) and `rvachevUp_of_pos` (Basic.lean:112), so it compiles unchanged there; Monotonicity.lean:294-295, EffectiveFlatness.lean:105/108 and NowhereAnalytic.lean:52 keep working since all of them import Basic transitively.

Step 2. Immediately below it, add the complementary-CDF form:

/-- On the whole nonnegative ray, Rvachev's function is the complementary
Fabius CDF; no upper endpoint restriction is needed. -/
theorem rvachevUp_eq_one_sub_fabiusReal_of_nonneg
    (F : BoundedFabius) (hF : IsFabius F) {t : ℝ} (ht : 0 ≤ t) :
    rvachevUp F t = 1 - fabiusReal F t := by
  rw [rvachevUp_eq_fabiusReal_one_sub F ht, hF.symmetry_all t]

Step 3. Keep the public name and arity in LaplaceTransform.lean:35 as a wrapper, preserving the implicit ...

**Verifier.** The finding survives every check. (1) Signatures are quoted verbatim and all four locations exist: LaplaceTransform.lean:35 (the theorem, with `exact hF.symmetry t ht` on line 47 as the only consumer of the full Icc membership), Basic.lean:77 `IsFabius.symmetry_all` (unconditional in x), Basic.lean:112 `rvachevUp_of_pos`, Basic.lean:144 ...

#### `abs_one_sub_pow_sub_exp_quadratic_le` and its four integrated forms hold at `n = 0`, where both sides are identically zero

Confidence medium.  `EndpointLaplaceComparison.lean:243`, `EndpointLaplaceComparison.lean:353`, `EndpointLaplaceComparison.lean:374`, `EndpointLaplaceComparison.lean:460`, `EndpointLaplaceComparison.lean:772`

**Why.** At `n = 0`: `(1 - x) ^ 0 = 1`, `Real.exp (-(0 : ℝ) * x) = 1`, `1 - (0 : ℝ) * x ^ 2 / 2 = 1`, so the left side is `|1 - 1| = 0`; the right side is `16 * 1 * (0 * x ^ 3 + 0 ^ 2 * x ^ 4) = 0`, and `0 ≤ 0` holds. The `1 ≤ n` hypothesis is used only by the `nlinarith` steps of the `x ≤ 1/2` and `x > 1/2` branches, both of which become vacuous. The three integrated forms inherit the degenerate case verbatim (both integrands are identically zero), and `abs_halfMoment_sub_fabiusLaplace_secondOrder_le` ...

**Proposal.** Statements unchanged; only metadata/rationale corrected. Add the five primed lemmas exactly as proposed, keeping the current names as wrappers. Corrected locations: abs_one_sub_pow_sub_exp_quadratic_le' from :243, abs_integral_one_sub_pow_sub_exp_quadratic_le' from :353, abs_endpointMoment_sub_laplace_secondOrder_le' from :374, abs_unitEndpointMoment_sub_unitLaplace_secondOrder_le' from :460, abs_halfMoment_sub_fabiusLaplace_secondOrder_le' from :774 (not :772). Corrected rationale: the 1 ≤ n hypothesis is NOT vacuous in the x > 1/2 branch at n = 0 — `hy : 1/4 ≤ N * x ^ 2` (:338) and `hNx3 : 1/8 ≤ N * x ^ 3` (:340) are false there — so the n = 0 case must be discharged before the `by_cases hxhalf`, via `rcases Nat.eq_zero_or_pos n with rfl | hn` closing the first branch by `simp` (both sides reduce to 0) and re-deriving `have hn : 1 ≤ n := hn` for the second; the x ≤ 1/2 branch itself needs only `hN0 : 0 ≤ N`. The n = 0 case of the halfMoment form rests on `unitEndpointMoment_weightedSumDistribution_eq_halfMoment` at EndpointLaplaceComparison.lean:731 (not :770) together with ...

**Verifier.** Survives adversarial check. (1) All five declarations exist with the quoted signatures (the fifth is at line 774, not 772 — 772 is its docstring). (2) The n = 0 instance is genuinely true, not vacuous-by-luck: (1-x)^0 = 1 for every x including x = 1 (npow, 0^0 = 1), -(↑(0:ℕ))*x = 0 so Real.exp = 1, and 1 - 0*x^2/2 = 1, giving LHS = |1-1| = 0; RHS ...

### Cluster: moments-probability

#### IMPLEMENTED: the normalized half-moment identity is valid also at `n = 0`

Confidence high.  `AnalyticMoments.lean`, `PaperStatements.lean`, `Basic.lean`, `Arithmetic.lean`

**Why.** The identity is unconditionally true.  Four of its six former call
sites passed a literal successor and discharged positivity with `(by omega)`;
the other two already carried a positive-index hypothesis.

**Implementation.** To preserve the source-facing equation and public API, the
positive-index theorem keeps its original signature.  The additive theorem
`halfMoment_eq_integral_formula_all` handles `n = 0` from
`halfMoment_zero = halfMomentIntegral_zero = 1` and delegates successors to
the existing result.  Internal analytic and dyadic callers use this all-index
form, removing their repeated positivity side conditions.

**Verifier.** The zero branch is definitionally the normalized equality
`1 = 1`; the successor branch is exactly the already-verified positive-index
identity.  No integral with the exponent `n-1` is asserted at zero.

#### IMPLEMENTED: `weightedSumCDF_left_formula` uses only `x ≤ 1/2`; the `0 ≤ x` half of the `Icc` hypothesis is dead

Confidence high.  `ProbabilityRepresentation.lean:474`, `ProbabilityRepresentation.lean:532`, `ProbabilityRepresentation.lean:540`

**Why.** The `Icc` phrasing made the lemma look like a genuinely
interval-restricted statement, although it is a global identity on
`(-∞,1/2]`.  The two former call sites in `cdfAdmissible_fixed` built `Icc`
membership proofs whose lower-bound components were never used.

**Implementation.** The strengthened theorem is now
`weightedSumCDF_eq_intervalIntegral_of_le_half`:

/-- The smoothing equation collapses to a single integral from the origin
whenever `x ≤ 1/2`; no lower bound on `x` is needed, since the CDF vanishes
on the nonpositive axis, making the reversed-orientation integral over
`[2x, 0]` zero. -/
lemma weightedSumCDF_eq_intervalIntegral_of_le_half {x : ℝ} (hx : x ≤ 1 / 2) :
    weightedSumCDF x = ∫ t in (0 : ℝ)..(2 * x), weightedSumCDF t := by
  -- body unchanged except:
  have hlower : 2 * x - 1 ≤ 0 := by linarith   -- was: linarith [hx.2]

The original `weightedSumCDF_left_formula` name remains as a compatibility
wrapper on `Icc 0 (1/2)`.  Both branches of `cdfAdmissible_fixed` now use the
strong theorem directly, so they no longer manufacture unused lower bounds.
The negative-input endpoint behavior is genuine rather than vacuous: both the
CDF and the reversed-orientation integral vanish there.

#### Four public theorems carry hypotheses the author already marked unused with a leading underscore

Confidence high.  `StepApproximationLimit.lean:133`, `StepApproximationLimit.lean:140`, `StepMeasureBridge.lean:168`, `StepMeasureBridge.lean:183`

**Why.** These are the cleanest instances of finding class 1 in the cluster: the hypotheses are provably unused (Lean's linter forced the `_` prefix), yet each call site still has to manufacture them. In `intervalIntegral_stepApproximant_tendsto_of_le` the caller constructs `hinner : a + δ ≤ b - δ` at line 353 only to satisfy the dead binder, which in turn is why `δ` is defined as `min (ε/8) ((b-a)/4)` rather than simply `ε/8`.

**Proposal.** Four public theorems carry provably unused hypotheses (author-marked with a leading underscore); the statements are true without them, so add hypothesis-free primed versions in the same modules and demote the current names to one-line wrappers:

StepApproximationLimit.lean (after line 145):
  theorem halfEndpointIntervalIndicator_monotoneOn_Iio_right' {a b : ℝ} :
      MonotoneOn (halfEndpointIntervalIndicator a b) (Iio b)
  theorem halfEndpointIntervalIndicator_antitoneOn_Ioi_left' {a b : ℝ} :
      AntitoneOn (halfEndpointIntervalIndicator a b) (Ioi a)
StepMeasureBridge.lean (after line 196):
  theorem intervalIntegral_rvachevUp_expand_sub_le' (F : BoundedFabius) (hF : IsFabius F)
      (a b δ : ℝ) (hδ : 0 ≤ δ) :
      (∫ x in (a - δ)..(b + δ), rvachevUp F x) - (∫ x in a..b, rvachevUp F x) ≤ 2 * δ
  theorem intervalIntegral_rvachevUp_sub_shrink_le' (F : BoundedFabius) (hF : IsFabius F)
      (a b δ : ℝ) (hδ : 0 ≤ δ) :
      (∫ x in a..b, rvachevUp F x) - (∫ x in (a + δ)..(b - δ), rvachevUp F x) ≤ 2 * δ

Proof route: copy the existing bodies unchanged (they never use the dead ...

**Verifier.** Core claim verified. All four declarations exist verbatim at the cited lines (StepApproximationLimit.lean:133,140; StepMeasureBridge.lean:168,183) with underscore-prefixed binders, and all four weakened statements are TRUE. Boundary check on the indicator lemmas: with halfEndpointIntervalIndicator a b x = if x = a or x = b then 1/2 else if a < x ...

### Cluster: papers-aggregates

#### `lemma_one` and `proposition_ten` carry a hypothesis `0 < x` that is implied by the next hypothesis and is already unused upstream

Confidence high.  `PaperStatements.lean:606`, `PaperStatements.lean:620`, `ScaleTranslation.lean:118`, `TaylorReduction.lean:131`

**Why.** `0 < x` is a strictly weaker consequence of `hlo`: `(2 : ℝ) ^ scale` is positive for every `scale : ℤ`, so `hlo` alone gives `0 < x`. The upstream proof already computes exactly this fact — `ScaleTranslation.lean:132` has `have haPos : 0 < a := by exact zpow_pos (by norm_num) scale` where `a = (2 : ℝ) ^ scale`. The redundancy is confirmed mechanically: `taylorRemainder_translate` names the binder `_hx` (never used), and in `extendedFabius_reduction` the only occurrence of `hx` in the whole ...

**Proposal.** Keep the finding only as a minimal in-place binder deletion in the two non-paper modules, and drop the paper-statement half entirely.

Do NOT add `taylorRemainder_translate_of_le` or `extendedFabius_reduction_of_le`: duplicating two theorems to shed one hypothesis that `lt_of_lt_of_le (zpow_pos (by norm_num : (0:ℝ) < 2) scale) hlo` recovers in one line is not worth two new declarations against five total call sites.

Do NOT change `lemma_one` (PaperStatements.lean:606) or `proposition_ten` (PaperStatements.lean:620) semantically. `0 < x` is the paper's own opening hypothesis in both Lemma L:taylor and Proposition P:Res (docs/papers/arXiv-1702.06487v3/157-Arithmetic-v3.tex), and PaperStatements.lean is a deliberate verbatim transcription that already preserves unused paper hypotheses as `_hn` binders (lines 635, 644, 687). At most rename `hx` to `_hx` in those two signatures, matching that existing convention.

The only defensible edit is deleting the dead binder where it is not a paper hypothesis:
- ScaleTranslation.lean:120 — remove `(_hx : 0 < x)` from `taylorRemainder_translate` ...

**Verifier.** The mathematical core survives verification: all four signatures are quoted verbatim and accurately; `0 < x` really is implied by `hlo` at every index (`(2:ℝ)^scale` is `zpow` with base 2, strictly positive for every `scale : ℤ` — never 0 even for negative exponents — and the file proves exactly this at ScaleTranslation.lean:131 with `zpow_pos`); ...

#### The first conjunct of `conjecture_sixteen_denominator_formulas` needs neither the conjecture nor `1 ≤ n`; it is an unconditional definitional identity

Confidence high.  `Paper06487Supplement.lean:417`, `Arithmetic.lean:606`, `Arithmetic.lean:610`, `Arithmetic.lean:614`

**Why.** Advertising the odd formula as conditional on Conjecture 16 overstates its logical cost: it is pure algebra in the definitions `normalizedDyadicDenominator n = dyadicDenominator n / 2 ^ n.choose 2` (Arithmetic.lean:606), `conjecturalK n = normalizedDyadicDenominator (2 * n - 1)` (610) and `conjecturalH n = conjecturalK n / (2 * (2*n-1)!)` (614) — unwinding gives `2 ^ (1 + c) * (2n-1)! * (D/(2^c) / (2 * (2n-1)!)) = D`. The evidence that neither hypothesis is used is in the file itself: the local ...

**Proposal.** The finding stands as written; only the "proof route" prose needs one factual correction. The existing second branch is not merely "the existing calc using `hconj.1 hn`" — it is (Paper06487Supplement.lean:438-458): `have ha := hconj.1 (n := n) hn` (named argument `(n := n)`, not a bare `hconj.1 hn`), followed by `unfold normalizedDyadicDenominator at ha`, the two `hpowEven`/`hpowOdd` `positivity` facts, and the three-step `calc`. All of that must be kept verbatim; only lines 425-435 (`have hoddFormula ...`) are deleted and line 437 becomes `exact dyadicDenominator_odd_eq_conjecturalH n`. The new standalone lemma is exactly the proposed text (the `hoddFormula` script with `m` renamed to `n` and `hm` dropped), placed immediately above `conjecture_sixteen_denominator_formulas`, which keeps its name, arity and binder names `(hconj : conjecture_sixteen) (n : ℕ) (hn : 1 ≤ n)`.

**Verifier.** Survives every check. (1) Signature verified verbatim at Paper06487Supplement.lean:417-424; the local `have hoddFormula (m : ℕ) (hm : 1 ≤ m)` at 425-435 really does never mention `hm` in its body, is used once (line 437), and `hconj` is used only in the second branch (line 438). (2) The three definitions exist exactly as quoted at ...

### Cluster: regularity

#### `up` is flat at the endpoints of its support: `1 < |x|` can be relaxed to `1 ≤ |x|`

Confidence high.  `GlobalBounds.lean:116`, `GlobalExtension.lean:309`

**Why.** The endpoint case `|x| = 1` is the mathematically interesting one: it is exactly the statement that `up` is a genuine C^∞ bump function (all derivatives vanish where the support closes), and it is the case the current strict hypothesis excludes. The strict form is only ever used through `abs_iteratedDeriv_rvachevUp_le` (GlobalBounds.lean:136), where the `|x| = 1` case is currently routed through the much heavier `iteratedDeriv_rvachev` + `abs_extendedFabius_le_one` branch.

**Proposal.** Add to `FabiusFunction.GlobalBounds`, immediately after the existing strict lemma:

/-- Every iterated derivative of Rvachev's function vanishes outside the open
support, including at the two endpoints `±1`. -/
theorem iteratedDeriv_rvachevUp_eq_zero_of_one_le_abs (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) {x : ℝ} (hx : 1 ≤ |x|) :
    iteratedDeriv n (rvachevUp F) x = 0

Proof structure (the finding's route (a) needs one fix — it cannot be combined with demoting the strict lemma to a wrapper, because the closure argument consumes the strict statement, and the `nhds`-filter argument that proves it genuinely fails at |x| = 1 since `up` is nonzero on all of `(-1,1)`). Two consistent options:

(i) Keep `iteratedDeriv_rvachevUp_eq_zero_of_one_lt_abs` as the primitive with its current proof, and derive the new lemma from it by the closure argument: `Continuous (iteratedDeriv n (rvachevUp F))` from `rvachev_contDiff F hF` (Differential.lean:260), `isClosed_eq` for `{y | iteratedDeriv n (rvachevUp F) y = 0}`, then `closure_Ioi 1 = Ici 1` and `closure_Iio (-1) = Iic (-1)`, splitting ...

**Verifier.** All three refutation grounds fail. (1) Signatures are quoted correctly: GlobalBounds.lean:116 is exactly `theorem iteratedDeriv_rvachevUp_eq_zero_of_one_lt_abs (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) {x : ℝ} (hx : 1 < |x|)`, and GlobalExtension.lean:309 is `iteratedDeriv_rvachev … (hx : x ∈ Icc (-1:ℝ) 1) : iteratedDeriv n (rvachevUp F) x = 2 ...

#### `fabiusReal` is flat at the right endpoint: `1 < x` can be relaxed to `1 ≤ x`

Confidence high.  `BoundedDerivatives.lean:72`, `BoundedDerivatives.lean:53`

**Why.** The file already states flatness at the *left* endpoint (`iteratedDeriv_fabiusReal_zero`, line 53) and its module header advertises `F` as gluing C^∞ to the two constant tails, but the mirror statement at `x = 1` — the one that actually makes that gluing a theorem — is missing, and the strict hypothesis `1 < x` is precisely what excludes it. `Paper06487Supplement.iteratedDeriv_extendedFabius_one_eq_zero` records the analogous fact for `extendedFabius`, so the bounded version is the gap.

**Proposal.** Add to `FabiusFunction.BoundedDerivatives`, immediately after `iteratedDeriv_fabiusReal_eq_zero_of_one_lt` (BoundedDerivatives.lean:72). Leave that lemma exactly as it is, with its own `Ioi_mem_nhds` / `iteratedDeriv_const_succ` proof — do NOT convert it into a wrapper around the new theorem, since the new proof consumes it and the two would be mutually circular. The existing name therefore survives unchanged for its two current call sites (line 115 and any downstream user).

/-- Every positive-order derivative of the bounded Fabius function vanishes on
`[1, ∞)`: the open ray is handled by local constancy and the endpoint by
continuity, since `Ici 1` is the closure of `Ioi 1`. -/
theorem iteratedDeriv_fabiusReal_eq_zero_of_one_le (F : BoundedFabius)
    (hF : IsFabius F) (m : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    iteratedDeriv (m + 1) (fabiusReal F) x = 0 := by
  have hcont : Continuous (iteratedDeriv (m + 1) (fabiusReal F)) :=
    hF.contDiff.continuous_iteratedDeriv (m + 1)
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl (m + 1))
  have hclosed : IsClosed {y : ℝ | iteratedDeriv (m + ...

**Verifier.** I could not refute this. All five checks pass.

(1) Signature check — exact. `C:\ProveIt\.claude\worktrees\fabius-function-theorems-494024\Analysis\FabiusFunction\Lean\FabiusFunction\BoundedDerivatives.lean:72-78` is verbatim `theorem iteratedDeriv_fabiusReal_eq_zero_of_one_lt (F : BoundedFabius) (hF : IsFabius F) (m : ℕ) {x : ℝ} (hx : 1 < x) : ...

#### `hk : 1 ≤ k` is unnecessary in the two sharp-supremum theorems for `fabiusReal`

Confidence high.  `BoundedDerivatives.lean:119`, `BoundedDerivatives.lean:135`

**Why.** `k = 0` is true, not degenerate: `(2:ℝ)^0 = 1`, `iteratedDeriv 0 (fabiusReal F) 1 = fabiusReal F 1 = 1`, and `(0+1).choose 2 = 0` so the right-hand side is `2^0 = 1`. The companion statements for `extendedFabius` (GlobalBounds.lean:78, 90) and for `rvachevUp` (GlobalBounds.lean:150, 167) are already stated for every `n : ℕ` with no hypothesis, so `fabiusReal` is the only one of the three families carrying a spurious side condition — an asymmetry a reader will read as a genuine failure at `k = ...

**Proposal.** Weaken the two theorems in place rather than adding `_all` duplicates with wrappers. In BoundedDerivatives.lean:

theorem iteratedDeriv_fabiusReal_inv_two_pow (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) :
    iteratedDeriv k (fabiusReal F) (((2 : ℝ) ^ k)⁻¹) = 2 ^ (k + 1).choose 2

theorem isGreatest_abs_iteratedDeriv_fabiusReal (F : BoundedFabius)
    (hF : IsFabius F) (k : ℕ) :
    IsGreatest (Set.range fun x : ℝ => |iteratedDeriv k (fabiusReal F) x|)
      (2 ^ (k + 1).choose 2)

Proof of the first: replace `obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩` (line 122) with `match k with | 0 => ... | (j + 1) => ...`; the `j + 1` branch is lines 123-131 verbatim. The `0` branch must rewrite `pow_zero` before `inv_one` (the sketch's `rw [iteratedDeriv_zero, inv_one, ...]` will not fire on `((2:ℝ)^0)⁻¹`); e.g. `rw [iteratedDeriv_zero, pow_zero, inv_one, hF.one_of_one_le 1 le_rfl, show ((0:ℕ)+1).choose 2 = 0 from by decide, pow_zero]`. Alternatively route the whole `0` branch through the existing `fabiusReal_eq_extendedFabius_of_le_one F hF (le_refl 1)` plus ...

**Verifier.** Verified and confirmed. (1) Both declarations exist at BoundedDerivatives.lean:119 and :135 with exactly the quoted signatures, including `(hk : 1 ≤ k)`. (2) The boundary case k = 0 is genuinely true, not degenerate: `(2:ℝ)^(0:ℕ) = 1` and `1⁻¹ = 1`, so the LHS is `iteratedDeriv 0 (fabiusReal F) 1 = fabiusReal F 1`, and `IsFabius.one_of_one_le : ∀ ...

#### Both flatness `IsLittleO` statements hold on the full neighbourhood filter, not just the one-sided one

Confidence high.  `FabiusFlatness.lean:53`, `FabiusFlatness.lean:75`, `FabiusFlatness.lean:41`

**Why.** The one-sided restriction is an artifact of the proof, not of the mathematics: `fabiusReal F` is identically `0` on `(-∞, 0]` and identically `1` on `[1, ∞)`, so the estimate is trivially true on the missing side. The file already proves the two-sided statement for `extendedFabius` (line 41) and then *throws information away* at line 56 (`.mono (nhdsWithin_le_nhds …)`) before restoring the bounded function. Callers that want a genuine `nhds`-flatness (e.g. any Taylor/asymptotic argument at the ...

**Proposal.** Add two-sided versions to `FabiusFunction.FabiusFlatness` and demote the current names to one-line wrappers:

/-- The bounded Fabius function is little-o of every power at zero, from both sides. -/
theorem fabiusReal_isLittleO_pow_at_zero (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) : fabiusReal F =o[nhds 0] (fun x : ℝ => x ^ n) := by
  refine (extendedFabius_isLittleO_pow_at_zero F hF n).congr' ?_ EventuallyEq.rfl
  -- note the orientation: `congr'` needs `f₁ =ᶠ[l] f₂`, i.e. extended ⇒ bounded
  filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with y hy
  by_cases hy0 : y ≤ 0
  · rw [extendedFabius_eq_zero_of_nonpos F hF hy0, hF.zero_of_nonpos y hy0]
  · exact extendedFabius_eq_fabiusReal F hF ⟨le_of_lt (lt_of_not_ge hy0), hy.le⟩

/-- The complementary function is little-o of every power of the distance to one, from both sides. -/
theorem one_sub_fabiusReal_isLittleO_pow_at_one (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) :
    (fun x : ℝ => 1 - fabiusReal F x) =o[nhds 1] (fun x : ℝ => (1 - x) ^ n) := by
  have hreflect : Tendsto (fun x : ℝ => 1 - x) (nhds 1) ...

**Verifier.** All three cited locations check out verbatim. `FabiusFlatness.lean:41` is `extendedFabius_isLittleO_pow_at_zero : extendedFabius F =o[nhds 0] (fun x : ℝ => x ^ n)`; `:53` and `:75` carry exactly the quoted one-sided signatures, and `:58` really does discard the two-sided filter via `.mono (nhdsWithin_le_nhds (s := Ici (0:ℝ)))`.

The weakened ...

#### Strict monotonicity/antitonicity of `F'` holds on the closed halves, not only the open ones

Confidence high.  `Convexity.lean:97`, `Convexity.lean:108`, `Monotonicity.lean:291`, `Monotonicity.lean:301`

**Why.** The proofs already push the arguments into *closed* intervals: `strictMonoOn_rvachevUp` is stated on `Icc (-1) 0` and `strictAntiOn_rvachevUp` on `Icc 0 1`, and `x ↦ 2x - 1` maps `Icc 0 (1/2)` onto exactly `Icc (-1) 0` and `Icc (1/2) 1` onto exactly `Icc 0 1`. So the `Ioo` in the statement discards information the proof already has. The endpoint content is not vacuous: it yields `F'(0) = 0 < F'(x) < F'(1/2) = 2` for `x` strictly inside, and `deriv (fabiusReal F)` injective on each closed half.

**Proposal.** Add to FabiusFunction.Convexity, immediately before the existing Ioo lemmas:

theorem strictMonoOn_deriv_fabiusReal_Icc (F : BoundedFabius) (hF : IsFabius F) :
    StrictMonoOn (deriv (fabiusReal F)) (Icc (0 : R) (1 / 2))

theorem strictAntiOn_deriv_fabiusReal_Icc (F : BoundedFabius) (hF : IsFabius F) :
    StrictAntiOn (deriv (fabiusReal F)) (Icc (1 / 2 : R) 1)

with the existing proof bodies used unchanged (the two `show 2 * x - 1 in Icc (-1:R) 0 from <by linarith [hx.1], by linarith [hx.2]>` obligations are discharged by the same linarith calls from the non-strict Icc bounds; likewise `Icc (0:R) 1` in the antitone case).

Corrections to the finding as filed:
- There are TWO consumers, not one: strictConvexOn_fabiusReal_firstHalf (Convexity.lean:148) uses the Ioo mono lemma and strictConcaveOn_fabiusReal_secondHalf (Convexity.lean:163) uses the Ioo anti lemma. Both go through `rw [interior_Icc]`, so BOTH need `.mono Ioo_subset_Icc_self` if the Ioo names are dropped. Retaining the two existing names as one-line wrappers
    theorem strictMonoOn_deriv_fabiusReal ... := ...

**Verifier.** The finding survives every adversarial check. (1) Signatures are quoted verbatim: Convexity.lean:97-98 and :108-109 match exactly, and the cited ingredients Monotonicity.lean:291 (strictAntiOn_rvachevUp on Icc (0:R) 1) and :301 (strictMonoOn_rvachevUp on Icc (-1:R) 0) are genuinely stated on CLOSED intervals. (2) The weakened statement is TRUE at ...

#### The self-improving estimate `F(x) ≤ 2x·F(2x)` does not need `x ≤ 1/2`

Confidence high.  `EffectiveFlatness.lean:41`

**Why.** For `1/2 < x` the inequality is not merely true but trivially true, and stating it only on `[0, 1/2]` makes the estimate look like a genuine interval restriction when it is not. Since `fabiusReal_le_two_pow_mul_pow` (line 67) has to re-derive `hhalf : x ≤ 1/2` from its dyadic hypothesis `2 ^ n * x ≤ 1` by `nlinarith` at each induction step, the unrestricted form removes that obligation from the induction.

**Proposal.** Add to `FabiusFunction.EffectiveFlatness`, keeping the current name as a wrapper that discards `hx`:

/-- The self-improving estimate `F(x) ≤ 2x F(2x)` holds on the whole half line. -/
theorem fabiusReal_le_two_mul_mul_of_nonneg (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx0 : 0 ≤ x) :
    fabiusReal F x ≤ 2 * x * fabiusReal F (2 * x)

**Verifier.** Could not refute; the finding survives every check.

1. Signature is quoted verbatim. `C:/ProveIt/.claude/worktrees/fabius-function-theorems-494024/Analysis/FabiusFunction/Lean/FabiusFunction/EffectiveFlatness.lean:41-43` reads exactly `theorem fabiusReal_le_two_mul_mul (F : BoundedFabius) (hF : IsFabius F) {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : ...

### Cluster: saddle

#### `hbexp : Real.exp 1 ≤ b` is implied by the `4 ≤ b` / `16 ≤ b` hypothesis sitting right next to it

Confidence high.  `FabiusSaddleTail.lean:611`, `FabiusSaddleTail.lean:659`

**Why.** `Real.exp 1 < 2.72 < 4 ≤ b`, so the extra hypothesis carries no information. It forces every caller of the public theorem to produce two separate lower bounds on `b` where one suffices, and the module already knows the trick — `FabiusSaddleReferenceTail.lean:216` writes `(by have := Real.exp_one_gt_d9; linarith : (1:ℝ) ≤ Real.exp 1).trans hb` for exactly this purpose. `integral_scaledPolynomialKernel_standardRadius_le` moreover has no callers anywhere in the 174 modules, so its signature is ...

**Proposal.** Edit both declarations IN PLACE in FabiusSaddleTail.lean. Do not introduce primed names or compatibility wrappers: `integral_scaledPolynomialKernel_standardRadius_le` has zero callers anywhere, and `integral_norm_fabius_scaledSaddleKernel_standardRadius_le` has exactly one, at FabiusSaddleTail.lean:735 in the same file, which is edited in the same commit.

Step 1 (required, and missing from the original finding): add `import Mathlib.Analysis.Complex.ExponentialBounds` to the header of FabiusSaddleTail.lean. Without it `Real.exp_one_lt_d9` is not in scope. The edge is cheap — ExponentialBounds is a small leaf whose own three imports (`Mathlib.Analysis.Complex.Exponential`, `Mathlib.Analysis.SpecialFunctions.Log.Deriv`, `Mathlib.Analysis.SpecialFunctions.Pow.Real`) are all already in FabiusSaddleTail's cone, verified.

Step 2 (line 611): drop `(hbexp : Real.exp 1 ≤ b)`, keep `(hb4 : 4 ≤ b)`, and insert as the first proof line
  `have hbexp : Real.exp 1 ≤ b := by have := Real.exp_one_lt_d9; linarith`
The rest of the proof is unchanged; `hbexp` is used exactly three times there ...

**Verifier.** CORE SURVIVES, RATIONALE AND PROOF ROUTE ARE PARTLY FALSE.

Confirmed:
(1) Both declarations exist exactly at FabiusSaddleTail.lean:611 and :659, and the signatures are quoted verbatim and correctly.
(2) The weakening is mathematically true with no boundary case: `b` is a real constrained by `4 ≤ b` (resp. `16 ≤ b`), and `Real.exp 1 < 2.7182818286 ...

### Cluster: thuemorse-qbinomial

#### `norm_binaryReductionRemainder_le` does not need `1 ≤ N`, and `norm_globalBinaryReductionSummand_le_ge_two` then needs only `1 ≤ m`, not `2 ≤ m`

Confidence high.  `FabiusBinaryReductionSeries.lean:444`, `FabiusBinaryReductionSeries.lean:479`, `FabiusBinaryReductionSeries.lean:505`

**Why.** `hN : 1 ≤ N` exists only to route through the private half-interval bound of finding 1; with the general `fabiusReal_le_two_mul` the bound holds at `N = 0` too (`binaryTail x 0 < 1`, so the remainder is at most `2 = 2 * (2^0)⁻¹`). The `2 ≤ m` in the second theorem is then only needed to supply `1 ≤ m - 1`, so it drops to `1 ≤ m`. This also lets `summable_norm_globalBinaryReductionSummand` (:505) shift by 1 instead of 2. The current name `..._le_ge_two` bakes the removable hypothesis into the ...

**Proposal.** Keep both weakenings as proposed, but fix the proof route, which as stated does not typecheck.

New declarations:
`theorem norm_binaryReductionRemainder_le' (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) (hx0 : 0 ≤ x) (N : ℕ) : ‖binaryReductionRemainder F x N‖ ≤ 2 * ((2 : ℝ) ^ N)⁻¹`
`theorem norm_globalBinaryReductionSummand_le_of_one_le (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) (hx0 : 0 ≤ x) (m : ℕ) (hm : 1 ≤ m) : ‖globalBinaryReductionSummand x m‖ ≤ 4 * ((2 : ℝ) ^ (m - 1))⁻¹`
Retain `norm_binaryReductionRemainder_le` and `norm_globalBinaryReductionSummand_le_ge_two` as wrappers (the second discharging `1 ≤ m` from `2 ≤ m`, e.g. `fun F hF x hx0 m hm => norm_globalBinaryReductionSummand_le_of_one_le F hF x hx0 m (le_trans one_le_two hm)`), so the existing consumer `summable_norm_globalBinaryReductionSummand` and `FabiusGlobalQBinomialSeries.lean:96` are unaffected.

Proof-route correction: `fabiusReal_le_two_mul` lives in `Regularity.lean:111`, and `Regularity` is NOT in the transitive import closure of `FabiusBinaryReductionSeries.lean` (that closure is Arithmetic, Basic, ...

**Verifier.** All five checks pass. (1) Signatures are quoted accurately: :444 `norm_binaryReductionRemainder_le` really carries `(hN : 1 ≤ N)`, :479 `norm_globalBinaryReductionSummand_le_ge_two` really carries `(hm : 2 ≤ m)`, :505 really shifts by 2. (2) The boundary case is TRUE, not load-carrying: at N = 0, `binaryTail x 0 = x - ⌊x⌋₊ ∈ [0,1)` by ...

#### `neg_one_pow_thueMorseBit` is stated only over `ℚ` although its proof is generic in `[Ring R]`, forcing a private cast copy and three `map_pow, map_neg, map_one` detours

Confidence high.  `FabiusRawQBinomialFormula.lean:33`, `FabiusComplexShiftSpline.lean:59`, `FabiusQBinomialTaylor.lean:140`, `FabiusRawQBinomialScalar.lean:120`, `FabiusDyadicQBinomialScalar.lean:218`

**Why.** The proof uses only `neg_one_pow_eq_pow_mod_two`, which Mathlib states for `[Ring R]` (Mathlib/Algebra/Ring/Commute.lean:171) — `ℚ` is strictly stronger than the argument needs. The `ℚ`-only form forces (a) a private `ℂ` cast copy in FabiusComplexShiftSpline, (b) `rw [← neg_one_pow_thueMorseBit]; simp only [map_pow, map_neg, map_one, …]` at three `Field K`/`Algebra ℚ K` sites, and (c) a fourth open re-derivation inside `globalBinaryReductionCoefficient_cast` ...

**Proposal.** Add to ThueMorseBinomialLog.lean (upstream-most module defining `thueMorseBit`):

theorem neg_one_pow_thueMorseBit_ring {R : Type*} [Ring R] (r : ℕ) :
    (-1 : R) ^ thueMorseBit r = (thueMorseSign r : R) := by
  rw [thueMorseBit, thueMorseSign]
  push_cast
  exact (neg_one_pow_eq_pow_mod_two (R := R) (binaryWeight r)).symm

Then: (i) keep `neg_one_pow_thueMorseBit` (FabiusRawQBinomialFormula.lean:33) as the ℚ instance `neg_one_pow_thueMorseBit_ring (R := ℚ)` so its 4 downstream uses are untouched; (ii) delete the private `neg_one_pow_thueMorseBit_complex` (FabiusComplexShiftSpline.lean:59-61) and replace its two uses at lines 71 and 170 with `simp_rw [neg_one_pow_thueMorseBit_ring (R := ℂ)]`. That is the entire payoff: one deleted private alias plus a reusable ring-level lemma.

Explicitly DROP FabiusGlobalQBinomialSeries.lean:49 from the finding — `globalBinaryReductionCoefficient` is ℝ-valued and written with `(-1:ℝ)^binaryWeight`, contains no `thueMorseSign`, and its `neg_one_pow_eq_pow_mod_two` call is not a duplicate of this lemma; changing it would lengthen the proof. Same ...

**Verifier.** CORE SURVIVES, TWO OF THE SIX LOCATIONS AND THE STATED PAYOFF DO NOT.

Verified true:
1. Signatures quoted correctly. `neg_one_pow_thueMorseBit` is at FabiusRawQBinomialFormula.lean:33 verbatim; the private `neg_one_pow_thueMorseBit_complex` is at FabiusComplexShiftSpline.lean:59 verbatim (used by `simp_rw` at lines 71 and 170).
2. The ingredient ...

#### Four declarations in `FabiusQBinomialTaylor` carry a redundant `[CharZero K]`, inconsistently with the 36 sibling declarations in the same cluster

Confidence medium.  `FabiusQBinomialTaylor.lean:189`, `FabiusQBinomialTaylor.lean:204`, `FabiusQBinomialTaylor.lean:269`, `FabiusQBinomialTaylor.lean:323`

**Why.** `Field K` + `Algebra ℚ K` already implies `CharZero K`, and the module's own defs (`qBinomialThueMorseTranslatedNumeratorIn`, `fabiusReductionSumIn`, `qBinomialFabiusReductionPolynomial`) are all declared without it. The first two theorems' proofs are pure `congrArg (algebraMap ℚ K)` + `map_div₀` and never touch characteristic. The inconsistency also makes `qBinomialFabiusReductionPolynomial_zero` (`[CharZero K]`) harder to apply than `qBinomialFabiusReductionPolynomial_eq_sum` (no `[CharZero ...

**Proposal.** Drop `[CharZero K]` from all four declarations in FabiusQBinomialTaylor.lean (lines 189, 204, 269, 323), leaving `{K : Type*} [Field K] [Algebra ℚ K]` to match the 36 sibling declarations.

- `qBinomialThueMorseTranslatedNumeratorIn_div_eq_halfMoment` (189) and `qBinomialThueMorseTranslatedNumeratorIn_div_eq_fabiusAtInverseTwoPow` (204): remove the binder only; their proofs are `congrArg (algebraMap ℚ K)` + `map_div₀` over lemmas that are themselves CharZero-free, and use no simp/norm_num/field_simp, so no proof edit is needed.

- `qBinomialFabiusReductionPolynomial_eq_reductionSumIn` (269): remove the binder and open the proof with

    haveI : CharZero K := algebraRat.charZero K

  (note the EXPLICIT `K` — `algebraRat.charZero` is stated under `variable (R : Type*) [Nontrivial R]` at Mathlib/Algebra/CharP/Algebra.lean:145, so the argument-free form `algebraRat.charZero` does not elaborate). This is required only by `field_simp [Nat.cast_ne_zero]` at line 300, since `Nat.cast_ne_zero` (Mathlib/Algebra/CharZero/Defs.lean:74) is gated on `[CharZero R]`. `Field K` supplies both the ...

**Verifier.** The finding survives adversarial verification on all five checks.

(1) SIGNATURES VERIFIED. All four declarations sit at exactly the cited lines of FabiusQBinomialTaylor.lean (189, 204, 269, 323) with binders byte-identical to the quoted `{K : Type*} [Field K] [CharZero K] [Algebra ℚ K]`. No misquote.

(2) THE WEAKENING IS TRUE; NO BOUNDARY CASE ...

## Missing corollaries

### Cluster: discrete-limits-computability

#### The centered spline has a stated left support edge but no right one: `fabiusUniformSpline p x = 1` near `x = 1` is missing

Confidence high.  `FabiusUniformSpline.lean:47`, `FabiusUniformSpline.lean:1186`, `FabiusUniformSpline.lean:1026`, `FabiusUniformSpline.lean:1199`

**Why.** The module already proves that the spline vanishes to the left of the first half-cell and, via the probabilistic model, that its CDF counterpart is one past the last half-cell — but only the vanishing half is exposed on `fabiusUniformSpline` itself. Without the right-edge statement the API is asymmetric and the sharp support interval `[2^-(p+1), 1 - 2^-(p+1)]` is only half visible. The endpoint value `fabiusUniformSpline p 1 = 1` is also the natural normalization companion of ...

**Proposal.** Keep both proposed declarations verbatim — they are true in every degree, p = 0 included:

/-- The centered spline is already saturated at one on the last half-cell of the fundamental
interval, in every degree. This is the exact mirror of `fabiusUniformSpline_eq_zero_of_le_half`. -/
theorem fabiusUniformSpline_eq_one_of_le (p : ℕ) {x : ℝ}
    (hx : 1 - 1 / (2 : ℝ) ^ (p + 1) ≤ x) (hx1 : x ≤ 1) :
    fabiusUniformSpline p x = 1

/-- Explicit right endpoint value of every centered finite spline. -/
theorem fabiusUniformSpline_one_eq_one (p : ℕ) : fabiusUniformSpline p 1 = 1

The stated proof route is sound as written (p = 0 via `fabiusUniformSpline_zero_eq_centeredPartialCDF_of_mem_Icc` at :1199, p = succ via `fabiusUniformSpline_eq_centeredPartialCDF` at :1026, both closed by `uniformCenteredPartialCDF_eq_one_of_le` at :1186), and the root-namespace alias should follow the `monotoneOn_fabiusUniformSpline_all` pattern at :1328.

Two corrections to the rationale:

(a) STRIKE the sentence "Note the identity extends by `fabiusUniformSpline_one_add` to the whole cell `[1 - 2^-(p+1), 1 + ...

**Verifier.** The finding survives verification on all five refutation tests, but its closing rationale sentence contains a false side claim that must be struck.

(1) Citations are accurate. `Fabius.fabiusUniformSpline_eq_zero_of_le_half (p : ℕ) (hp : 0 < p) {x} (hx : (2:ℝ)^p * x ≤ 1/2)` is at FabiusUniformSpline.lean:47 exactly as quoted; ...

### Cluster: dyadic

#### The exact value `F(2⁻ⁿ) = fabiusAtInverseTwoPow n` has no public statement, only a private one

Confidence high.  `DyadicAnalytic.lean:287`, `DyadicAnalytic.lean:443`, `AnalyticMoments.lean:451`

**Why.** `fabiusAtInverseTwoPow` is the corpus's central exact-value object — it appears in ExactInversePower, FabiusInverseDyadicClosedForm, FabiusQBinomialFormula, FabiusQBinomialTaylor, FabiusQBinomialScalarFormula and DyadicClosedForm — yet the single statement identifying it with the analytic value `F(2⁻ⁿ)` is `private`. Every consumer has to reconstruct it. AnalyticMoments.lean:451-460 does exactly that, opening `halfMoment_eq_fabius_formula` with `have h := fabiusDyadic_cast F hF n 1 ...

**Proposal.** Add, in DyadicAnalytic.lean immediately after `fabiusDyadic_cast` (line 443):

/-- The exact rational inverse-power value of equation (32) is the analytic
value at `2⁻ⁿ`. -/
theorem fabiusAtInverseTwoPow_cast (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) :
    (fabiusAtInverseTwoPow n : ℝ) = fabiusReal F (((2 : ℝ) ^ n)⁻¹) := by
  simpa [fabiusAtInverseTwoPow, one_div] using
    fabiusDyadic_cast F hF n 1 Nat.one_le_two_pow

**Verifier.** Finding survives adversarial checking on every axis.

(1) Citations accurate. DyadicAnalytic.lean:287 is `private theorem analyticInverseValue_eq_fabiusAtInverseTwoPow` with the quoted signature; its two helpers really are private (DyadicAnalytic.lean:24 `private def inverseTwoPowReal (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹`, :26 `private def ...

### Cluster: fourier-legendre

#### The unified derivative family is bridged to the explicit families only at k = 1; the k = 2,3,4 bridges are missing

Confidence medium.  `PeriodicSmooth.lean:56`, `PeriodicRegularity.lean:71`, `PeriodicRegularity.lean:75`, `PeriodicRegularity.lean:80`

**Why.** PeriodicSmooth's whole point is that it "upgrades the four-derivative API in `PeriodicRegularity` to `C∞`" (its own module header), yet the two APIs are connected at exactly one order. Without the k = 2,3,4 bridges the four explicit families in PeriodicRegularity remain a parallel, unreconciled development: nothing in the corpus records that `negativeLaplaceForwardTermFourth` really is the fourth member of the recursively generated family, and any consumer holding a `Fourth`-flavoured bound ...

**Proposal.** The finding stands; only the location and the tactic sketch need adjusting. Correct location: `negativeLaplaceForwardTermDeriv_one` is at PeriodicSmooth.lean:57 (not 56). Add immediately after it, in `PeriodicSmooth.lean` (namespace `Fabius`, `open Polynomial` already in scope):

@[simp] theorem forwardDerivativeQuotientPolynomial_one :
    forwardDerivativeQuotientPolynomial 1 = -1
@[simp] theorem forwardDerivativeQuotientPolynomial_two :
    forwardDerivativeQuotientPolynomial 2 = 1 + X
@[simp] theorem forwardDerivativeQuotientPolynomial_three :
    forwardDerivativeQuotientPolynomial 3 = -(1 + C 4 * X + X ^ 2)
@[simp] theorem negativeLaplaceForwardTermDeriv_two (s : ℝ) (n : ℕ) :
    negativeLaplaceForwardTermDeriv 2 s n = negativeLaplaceForwardTermSecond s n
@[simp] theorem negativeLaplaceForwardTermDeriv_three (s : ℝ) (n : ℕ) :
    negativeLaplaceForwardTermDeriv 3 s n = negativeLaplaceForwardTermThird s n
@[simp] theorem negativeLaplaceForwardTermDeriv_four (s : ℝ) (n : ℕ) :
    negativeLaplaceForwardTermDeriv 4 s n = negativeLaplaceForwardTermFourth s n

Proof route ...

**Verifier.** Every check confirms the finding. (1) Declarations exist as quoted: `negativeLaplaceForwardTermDeriv_one` at PeriodicSmooth.lean:57 (claim said 56 — off by one, immaterial) with exactly the quoted statement; `negativeLaplaceForwardTermSecond/Third/Fourth` verbatim at PeriodicRegularity.lean:71/75/80. (2) The proposed equalities are TRUE. ...

### Cluster: lambert-asymptotics

#### The lower-Lambert phase satisfies the sharp branch bound `1 / log 2 < λ`, which is not stated and is re-derived four times in weakened form

Confidence high.  `LowerLambertW.lean:70`, `LowerLambertW.lean:98`, `LowerLambertW.lean:103`, `FabiusSharpLambertMain.lean:24`, `FabiusLambertPhase.lean:44`

**Why.** `lowerLambertW_lt_neg_one` (LowerLambertW.lean:70) already gives `W(z) < -1` on `Ioo (-exp(-1)) 0`, and `paperLambertN x = -lowerLambertW (-(log 2 * x)) / log 2`, so the sharp bound `λ > 1/log 2 ≈ 1.4427` is immediate — but only `0 < λ` is ever recorded, and even that only in FabiusSharpLambertMain.lean, two modules downstream of `fabiusLambertPhase`'s definition and unusable from FabiusLambertPhase.lean, where positivity is instead re-derived three times by an identical five-line `nlinarith` ...

**Proposal.** Add to LowerLambertW.lean immediately after `paperLambertN_eq9` (after line 114), inside the existing `noncomputable section` of `namespace Fabius`; no new imports are needed.

/-- On its natural domain the paper's stationary point lies strictly beyond the
branch point `1 / log 2`; this is sharp, since `λ → 1 / log 2` as
`log 2 * x → exp (-1)`. -/
theorem one_div_log_two_lt_paperLambertN {x : ℝ} (hx : 0 < x)
    (hsmall : Real.log 2 * x < Real.exp (-1)) :
    1 / Real.log 2 < paperLambertN x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hz : -(Real.log 2 * x) ∈ Ioo (-Real.exp (-1)) 0 := by
    constructor <;> linarith [mul_pos hlog2 hx]
  have hW : 1 < -lowerLambertW (-(Real.log 2 * x)) := by
    linarith [lowerLambertW_lt_neg_one hz]
  rw [paperLambertN, lt_div_iff₀ hlog2]
  field_simp
  linarith

/-- Positivity of the paper's stationary point. -/
theorem paperLambertN_pos {x : ℝ} (hx : 0 < x)
    (hsmall : Real.log 2 * x < Real.exp (-1)) : 0 < paperLambertN x :=
  lt_trans (one_div_pos.mpr (Real.log_pos (by norm_num)))
    ...

**Verifier.** Every cited declaration exists at the stated line with the stated signature. `lowerLambertW_lt_neg_one` (LowerLambertW.lean:70) really is `W(z) < -1` on `Ioo (-exp(-1)) 0`, `paperLambertN x = -lowerLambertW (-(log 2 * x)) / log 2` (LowerLambertW.lean:98), and `log 2 > 0`, so `1/log 2 < paperLambertN x` follows in three lines from a hypothesis `hz` ...

#### The uncorrected Wikipedia formula fails not just the `O(1/(-log x))` rate but asymptotic equivalence itself — a two-line corollary of two theorems already in the cluster

Confidence medium.  `FabiusWikipediaObstruction.lean:83`, `FabiusWikipediaObstruction.lean:170`, `FabiusSharpAsymptotic.lean:52`, `FabiusSharpAsymptotic.lean:62`

**Why.** `¬ (f =O g)` with `g → 0` is strictly weaker than `¬ (f → 0)`: the latter implies the former, not conversely. The module header of FabiusSharpAsymptotic.lean says "Adding `negativeLaplacePsi` at the exact lower-Lambert phase gives an `O(1 / (-log x))` error; deleting it does not", but the source-facing question it answers is whether the printed formula is an asymptotic equivalent — and the corpus already proves the affirmative for the corrected formula ...

**Proposal.** Both theorem statements stand exactly as proposed. Only the proof route needs correction (and two line refs).

In FabiusWikipediaObstruction.lean, beside the Big-O version at line 170:

theorem fabiusWikipediaElementaryMain_error_not_tendsto_zero_of_corrected
    (q : ℝ → ℝ)
    (hcorrected : Tendsto (fun x : ℝ => q x - fabiusExplicitCorrectedWikipediaMain x)
        (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    ¬ Tendsto (fun x : ℝ => q x - fabiusWikipediaElementaryMain x)
        (nhdsWithin 0 (Ioi 0)) (nhds 0)

Route: `intro h; apply negativeLaplacePsi_comp_fabiusLambertPhase_not_tendsto_zero` (FabiusWikipediaObstruction.lean:85, not 83); `have hdiff := h.sub hcorrected` has limit `nhds (0 - 0)`, so normalize with `simpa` / `sub_zero`; then transport along `filter_upwards with x; simp only [fabiusExplicitCorrectedWikipediaMain, Function.comp_apply]; ring` — the identical congruence already written at FabiusWikipediaObstruction.lean:182-184, with `IsBigO.sub`/`trans_tendsto` replaced by `Tendsto.sub`/`Tendsto.congr'`.

In FabiusSharpAsymptotic.lean, beside line 51:

theorem ...

**Verifier.** All four citations check out: FabiusWikipediaObstruction.lean:85 is `negativeLaplacePsi_comp_fabiusLambertPhase_not_tendsto_zero` (cited line 83 is its docstring), line 170 is `fabiusWikipediaElementaryMain_error_not_isBigO_of_corrected_of_tendsto`, and FabiusSharpAsymptotic.lean:51/61 hold the two theorems quoted verbatim-correctly. The ...

### Cluster: negative-laplace

#### The finite-part integral identity already proves an unconditional sign for the Euler–Stieltjes combination: `gammaZetaConstant ≤ 0`, i.e. `γ₁ ≤ π²/12 − γ²/2`

Confidence high.  `BoseFinitePartIntegral.lean:536`, `BoseFinitePartIntegral.lean:33`, `BoseFinitePartIntegral.lean:37`, `StieltjesConstant.lean:130`, `NegativeLaplace.lean:52`

**Why.** The whole finite-part machinery of this module is built and then used only to compute one number; nothing records that the number's sign falls out for free. The sign is a genuine, nontrivial arithmetic fact about `γ`, `γ₁` and `π` (numerically `gammaZetaConstant ≈ -0.7287`) obtained here by a purely soft monotonicity argument, and `firstStieltjesConstant_le` is an unconditional numerical bound on `γ₁` that the corpus can currently state no other way.

**Proposal.** Keep the four proposed declarations as stated, with two adjustments to the write-up and one optional strengthening.

Proof-route correction: `boseFinitePartLargeKernel_nonpos` cannot cite line 439 as a reusable positivity fact — that line only produces `1 - Real.exp (-x) ≠ 0` inside the proof of `boseLogKernel_eq_negativeLaplaceKernel_add_log`. Re-derive it in place:
  `Real.log_nonpos (by linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx.le)]) (by linarith [Real.exp_nonneg (-x)])`
i.e. `0 ≤ 1 - exp (-x)` from `exp (-x) ≤ 1` and `1 - exp (-x) ≤ 1` from `Real.exp_nonneg`. Everything else in the route is correct as written: `div_nonpos_of_nonpos_of_nonneg (negativeLaplaceKernel_nonpos x hx) hx.le`, then `MeasureTheory.setIntegral_nonpos measurableSet_Ioc` / `measurableSet_Ioi` (which needs no integrability hypothesis), then rewrite by `boseFinitePartIntegral_eq_gammaZetaConstant`, then `unfold gammaZetaConstant; linarith`.

Rationale correction: describe `firstStieltjesConstant_le : γ₁ ≤ π²/12 - γ²/2` as the corpus's first unconditional numerical bound on γ₁, not as a sharp or ...

**Verifier.** Every element of the finding checks out. (1) Locations/signatures are verbatim: BoseFinitePartIntegral.lean:536 `boseFinitePartIntegral_eq_gammaZetaConstant` (no sorry), :33 `boseFinitePartSmallKernel x := negativeLaplaceKernel x / x`, :37 `boseFinitePartLargeKernel x := boseLogKernel x / x`; NegativeLaplace.lean:52 `theorem ...

### Cluster: papers-aggregates

#### The four `iteratedDeriv_extendedFabius_*_eq_zero` lemmas are special cases of a sharp iff at every natural argument, which the ingredients already prove

Confidence high.  `Paper06487Supplement.lean:165`, `Paper06487Supplement.lean:175`, `Paper06487Supplement.lean:193`, `Paper06487Supplement.lean:203`, `OriginalPaperSupplement.lean:194`

**Why.** The current family is a scattered set of `2 ^ scale`-shaped special cases of a single clean statement about all nonnegative integers, and it is not sharp: nothing in the corpus records that the derivative-vanishing *fails* at odd integers for `order = 0`, even though `paperTheta_odd_nat_eq` already computes that value as `(-1) ^ binaryWeight b`. The odd-integer non-vanishing is exactly what makes `iteratedDeriv_rvachev_centeredDyadic_ne_zero` (and hence `rvachev_not_analyticAt`) work, so the ...

**Proposal.** Keep the sharp characterisation, but state it in GlobalExtension.lean rather than OriginalPaperSupplement.lean, and drop the novelty claim about odd-integer non-vanishing.

theorem iteratedDeriv_extendedFabius_natCast_eq_zero_iff
    (F : BoundedFabius) (hF : IsFabius F) (order m : ℕ) :
    iteratedDeriv order (extendedFabius F) (m : ℝ) = 0 ↔ (1 ≤ order ∨ Even m)

plus the one-directional convenience form
theorem iteratedDeriv_extendedFabius_natCast_eq_zero
    (F : BoundedFabius) (hF : IsFabius F) (order m : ℕ) (h : 1 ≤ order ∨ Even m) :
    iteratedDeriv order (extendedFabius F) (m : ℝ) = 0.

Corrections to the finding as written:
1. Placement. Paper06487Supplement.lean imports only FabiusFunction.PaperStatements, and PaperStatements does not import OriginalPaperSupplement (its only importers are NowhereAnalytic.lean and Paper05442.lean). Putting the iff in OriginalPaperSupplement therefore forces a new cross-paper import edge Paper06487Supplement -> OriginalPaperSupplement before the four lemmas can be rewritten as instances. That edge would not cycle, but it is avoidable: every ...

**Verifier.** All seven cited declarations exist at the stated lines with the quoted signatures (Paper06487Supplement.lean:164/175/193/203; OriginalPaperSupplement.lean:51/194/214; the underlying iteratedDeriv_extendedFabius is GlobalExtension.lean:272). The proposed iff is TRUE and I checked it by hand at every boundary: rewriting by ...

#### `moment_nonneg` is not sharp: `0 < moment n` follows from lemmas already in the corpus, and `halfMoment_pos` already exists as the analogue

Confidence high.  `Paper06487Supplement.lean:31`, `Parity.lean:357`, `Arithmetic.lean:103`, `Arithmetic.lean:115`, `Arithmetic.lean:296`

**Why.** `moment n` is the `2n`-th moment of a strictly positive bump (`moment_eq_integral`, PaperStatements.lean:131), so strict positivity is the true statement; `0 ≤` is a strictly weaker fact that loses the `moment n ≠ 0` information needed whenever a moment appears in a denominator or a `padicValRat`. The corpus already has the exact analogue for the half moments — `Fabius.halfMoment_pos (n : ℕ) : 0 < halfMoment n` at Arithmetic.lean:296, used at TwoAdic.lean:319/405, PaperStatements.lean:582, ...

**Proposal.** Add, next to `moment_nonneg` in Paper06487Supplement.lean:31:

/-- Every moment `c_n` of Rvachev's function is strictly positive. -/
theorem moment_pos (n : ℕ) : 0 < moment n := by
  rw [moment_eq_momentNumerator_div]
  refine div_pos ?_ ?_
  · exact_mod_cast momentNumerator_pos n
  · exact_mod_cast Nat.mul_pos (oddDoubleFactorial_pos (n + 1))
      (evenMersenneProduct_pos n)

and keep `moment_nonneg` as `(moment_pos n).le`.

Two changes from the original proposal. First, drop the suggested alternative placement in Parity.lean: Parity.lean imports only FabiusFunction.Arithmetic (which imports Mathlib alone), so `moment_eq_momentNumerator_div` from NormalizedEvenMoments.lean is not in scope there and the proof would not compile. If an upstream home is wanted instead of Paper06487Supplement.lean, the upstream-most module where both `momentNumerator_pos` and `moment_eq_momentNumerator_div` are in scope is TwoAdic.lean (which imports both Parity and NormalizedEvenMoments), next to `moment_num_den_odd`. Second, pass the indices `(n + 1)` and `n` explicitly rather than `_`, so ...

**Verifier.** Every cited declaration exists at the stated line with the stated signature, quoted verbatim: moment_nonneg (Paper06487Supplement.lean:31, proof `rw [moment_eq_momentNumerator_div]; positivity`), momentNumerator_pos (Parity.lean:357), oddDoubleFactorial_pos (Arithmetic.lean:103), evenMersenneProduct_pos (Arithmetic.lean:115), halfMoment_pos ...

#### `theorem_nine_all` records only naturality at `n = 0`, but `IsOddNatural (reshetnikov n)` holds for every `n` — the `n = 0` case has the same one-line proof

Confidence high.  `Paper06487Supplement.lean:213`, `PaperStatements.lean:708`, `Arithmetic.lean:179`

**Why.** The supplement's stated purpose is that "several lemmas deliberately expose stronger boundary cases or weaker hypotheses than the prose needs", and it already does exactly this for Theorem 9. Theorem 21's oddness conjunct is the strictly stronger fact (`IsOddNatural q = ∃ m, Odd m ∧ q = m`, Arithmetic.lean:179, implies `IsNatural q`) and the same `n = 0` boundary case is available, so `theorem_nine_all` is currently a weaker statement than the corpus can prove. Note the *second* conjunct of ...

**Proposal.** Title (corrected): `theorem_nine_all` records naturality only, but the strictly stronger `IsOddNatural (reshetnikov n)` holds for every `n` — including the `n = 0` boundary, which has the same one-line proof.

Add to `Paper06487Supplement.lean`, immediately BEFORE `theorem_nine_all` (line 213) so the optional re-derivation below is well-ordered:

/-- The literal all-index form of the oddness half of Theorem 21: every
Reshetnikov number, including `R_0 = 1`, is an odd natural number.  This
subsumes `theorem_nine_all`.  Only the oddness conjunct extends to `n = 0`;
the valuation conjunct of `theorem_twenty_one` genuinely needs `1 ≤ n`,
since at `n = 0` its left side is `0` and its right side is `-1`. -/
theorem theorem_twenty_one_odd_all (n : ℕ) : IsOddNatural (reshetnikov n) := by
  cases n with
  | zero =>
      refine ⟨1, odd_one, ?_⟩
      norm_num [reshetnikov, fabiusAtInverseTwoPow, fabiusDyadic,
        thueMorseSign, binaryWeight, evenMersenneProduct]
  | succ n => exact (theorem_twenty_one (n + 1) (by omega)).1

Optionally re-derive the existing `theorem_nine_all n` as
`let ...

**Verifier.** Survives every check. (1) All three cited declarations exist at the exact cited lines with the quoted signatures: Paper06487Supplement.lean:213 `theorem_nine_all (n : ℕ) : IsNatural (reshetnikov n)`; PaperStatements.lean:708 `theorem_twenty_one (n : ℕ) (hn : 1 ≤ n) : IsOddNatural (reshetnikov n) ∧ padicValRat 2 (fabiusAtInverseTwoPow n) = ...

### Cluster: thuemorse-qbinomial

#### The sharp converse of `qPochhammer_two_pow_eq_zero` is missing: the `q = 1/2` q-binomial polynomial has exactly the `n` roots `1, 2, 4, …, 2^(n-1)`

Confidence high.  `HalfQBinomial.lean:457`, `HalfQBinomial.lean:465`, `HalfQBinomial.lean:382`, `HalfQBinomial.lean:448`

**Why.** The corpus proves the vanishing direction (`qPochhammer_two_pow_eq_zero`, `halfQBinomial_two_pow_sum_eq_zero`) and the value at the first non-root (`halfQBinomial_two_pow_sum_eq_self`), but never records that those are *all* the roots. That is exactly the sharpness statement that makes the dyadic-node interpolation in `FabiusQBinomialFormula` (`qWeight_nodes_zero` / `qWeight_nodes_self`, FabiusQBinomialFormula.lean:262/280) non-degenerate: the weights `qWeight n k` are the unique-up-to-scale ...

**Proposal.** Add to HalfQBinomial.lean (after `qPochhammer_two_pow_eq_zero`, actual line 518 — the finding's cited line numbers 457/465/382/448 are stale by 61 lines from commit 4c59369fe's header docstring; the true anchors are 518, 526, 443, 509):

`theorem finiteQPochhammer_half_eq_zero_iff (z : ℚ) (n : ℕ) : finiteQPochhammer z (1 / 2) n = 0 ↔ ∃ j < n, z = (2 : ℚ) ^ j`

and the q-binomial form

`theorem halfQBinomial_pow_sum_eq_zero_iff (z : ℚ) (n : ℕ) : (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (1 / 2 : ℚ) ^ (k.choose 2) * halfQBinomial n k * z ^ k) = 0 ↔ ∃ j < n, z = (2 : ℚ) ^ j`,

plus — to match the module's established twin-naming convention, where every `halfQBinomial_*` result has a Wolfram-notation restatement (`qBinomial_half_theorem`, `qBinomial_half_two_pow_sum_eq_zero`) — a `qPochhammer_half_eq_zero_iff` alias and the contrapositive `finiteQPochhammer_half_ne_zero_iff`.

Also drop `private` from `qPochhammer_two_pow_self_eq_mersenne` (line 526): `qPochhammer ((2:ℚ)^n) (1/2) n = (-1)^n * halfMersenneProduct n`, i.e. ∏_{j<n}(1 - 2^(n-j)) = (-1)^n ∏_{j=1}^n (2^j - 1) — the value at ...

**Verifier.** All five checks pass. (1) Every cited declaration exists with the exact quoted signature; the line numbers are uniformly stale by 61 because commit 4c59369fe inserted exactly 61 header-docstring lines (verified via git numstat). Real locations: qPochhammer_two_pow_eq_zero:518, qPochhammer_two_pow_self_eq_mersenne:526 (indeed `private`), ...

## Deduplication

### Cluster: core

#### Rvachev's refinement equation is proved twice, once for a general `IsFabius` candidate and once for the fixed point

Confidence high.  `Differential.lean:148`, `Differential.lean:156`, `Differential.lean:166`, `Existence.lean:552`, `Existence.lean:566`

**Why.** Existence.lean:566-632 is a line-for-line transcription of Differential.lean:166-230: same trichotomy on `x`, same `hl`/`hr` one-sided derivatives glued with `.union` and `Iic_union_Ici`, same `comp_const_sub` + evenness step, differing only in `F`/`hF` being replaced by `boundedCandidate` and its ad hoc lemmas. The private helpers `rvachev_hasDerivAt_of_neg` (Differential.lean:156) and `rvachevCandidate_hasDerivAt_of_neg` (Existence.lean:552) are likewise the same proof twice. The duplication ...

**Proposal.** Same finding, with the substitution recipe corrected. Add to Differential.lean, immediately before `rvachev_hasDerivAt`, generalizing BOTH private helpers as well as the theorem:

```
private lemma rvachevUp_left_hasDerivAt_of_hasDerivAt (F : BoundedFabius)
    (hderiv : ∀ x : ℝ, HasDerivAt (fabiusReal F) (2 * rvachevUp F (2 * x - 1)) x)
    {x : ℝ} (_hx : x ≤ 0) :
    HasDerivAt (fun y : ℝ => fabiusReal F (y + 1)) (2 * rvachevUp F (2 * x + 1)) x

private lemma rvachevUp_hasDerivAt_of_neg_of_hasDerivAt (F : BoundedFabius)
    (hderiv : ∀ x : ℝ, HasDerivAt (fabiusReal F) (2 * rvachevUp F (2 * x - 1)) x)
    {x : ℝ} (hx : x < 0) :
    HasDerivAt (rvachevUp F) (2 * rvachevUp F (2 * x + 1)) x

/-- Rvachev's refinement equation follows from the global Fabius derivative
identity together with vanishing on the left tail; no smoothness, symmetry or
fixed-point information is used. -/
theorem rvachevUp_hasDerivAt_of_fabiusReal_hasDerivAt (F : BoundedFabius)
    (hzero : ∀ x : ℝ, x ≤ 0 → fabiusReal F x = 0)
    (hderiv : ∀ x : ℝ, HasDerivAt (fabiusReal F) (2 * rvachevUp F (2 * x - 1)) x)
    ...

**Verifier.** All five cited declarations exist at the stated lines with the quoted signatures (Differential.lean:148/156/166; Existence.lean:552/566), and the supporting lemmas the proposal names are real (`IsFabius.zero_of_nonpos` = Basic.lean:67, `rvachevUp_even` = Basic.lean:155 and genuinely hypothesis-free, `boundedCandidate_zero_of_nonpos` = ...

#### The Pascal step `C(n+2,2) = C(n+1,2) + (n+1)` is re-proved inline in 12 modules while a private lemma for it already exists

**DONE** in `1ea3554f4`.  `choose_succ_two`, `two_mul_choose_two_add` and `choose_add_two_two` are now public in `Arithmetic.lean`; all ten private copies are deleted and all eighteen call sites rewired in that one commit.  `Arithmetic` compiles green at that SHA (`lake build +FabiusFunction.Arithmetic`, 1053 jobs, exit 0, no warnings).  Note that building `Arithmetic` alone does not exercise the rewired call sites, which live downstream; `FabiusDiscreteLimitComplexShift` (1 Fabius dependency), `DyadicAnalytic` (6) and `FabiusQBinomialTaylor` (43) between them cover all three lemmas.

Confidence high.  `DyadicAnalytic.lean:60`, `GlobalExtension.lean:287`, `GlobalExtension.lean:359`, `DyadicClosedForm.lean:58`, `DyadicClosedForm.lean:584`

**Why.** Fourteen verbatim copies of a three-line `Nat.choose` identity, two of them inside a single file of my cluster (GlobalExtension.lean:287 in `iteratedDeriv_extendedFabius` and GlobalExtension.lean:359 in `iteratedDeriv_rvachev`), plus an existing private lemma nobody outside DyadicAnalytic can reach. This is pure arithmetic with no Fabius content and belongs in the exact-arithmetic layer.

**Proposal.** Add ONE lemma to Arithmetic.lean (confirmed: it already imports `Mathlib.Data.Nat.Choose.Basic`, and all 21 affected modules transitively import it), stating the fact in the *general* `(n+1)` shape so it covers both families, and pick a name not already used in the corpus (`choose_two_succ` is taken by the private lemma at FabiusDiscreteLimitComplexShift.lean:201):

```
/-- Second-column Pascal step: `C(n+1,2) = C(n,2) + n`.  This is the exponent
recurrence behind `2 ^ (n+1).choose 2` in every iterated-derivative and
dyadic-scale formula. -/
theorem choose_two_succ_left (n : ℕ) :
    (n + 1).choose 2 = n.choose 2 + n := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ]
  simp [Nat.choose_one_right, Nat.add_comm]
```

The `(n+2)` form used at the 12 iterated-derivative sites is then `choose_two_succ_left (n + 1)`, definitionally matching both the `(n+2).choose 2` and the `(n+1+1).choose 2` spellings, so no `show n + 1 + 1 = n + 2 by omega` step is needed at any site.

Then replace:
- 12 verbatim inline `have hchoose`/`have htop` blocks by `choose_two_succ_left _` (or ...

**Verifier.** The core claim survives, but two cited locations are wrong and the proposal has a name collision.

CONFIRMED:
1. `DyadicAnalytic.lean:60-64` — `private lemma choose_succ_two_step` exists verbatim as quoted (`simp [Nat.add_comm]`).
2. `GlobalExtension.lean:287-290` (inside `iteratedDeriv_extendedFabius`, decl at 273) and ...

#### AnalyticMoments re-declares three Rvachev boundary lemmas that Basic.lean already exports

Confidence high.  `AnalyticMoments.lean:23`, `AnalyticMoments.lean:28`, `AnalyticMoments.lean:33`, `AnalyticMoments.lean:38`, `Basic.lean:144`

**Why.** Basic.lean's own section header says these lemmas were collected next to the definition precisely to avoid "the four separate re-derivations that previously appeared downstream"; AnalyticMoments.lean is one that was missed. It imports `FabiusFunction.Differential`, hence `Basic`, so all three public lemmas are already in scope. The proof bodies are character-for-character the same up to the `if_pos`/`if_neg` argument spelling.

**Proposal.** Delete AnalyticMoments.lean:23-36 (the three private `rvachev_eq_zero_of_le_neg_one` / `rvachev_eq_zero_of_one_le` / `rvachev_zero` lemmas) and rewrite the references to the public Basic.lean names `rvachevUp_eq_zero_of_le_neg_one`, `rvachevUp_eq_zero_of_one_le`, `rvachevUp_zero`. Correction to the counts: this is 14 LINES but 16 occurrences — lines 134 and 602 each contain two calls (`rvachev_eq_zero_of_one_le F hF le_rfl, rvachev_zero F hF`). Argument order is unchanged in every case, since both versions bind `(F) (hF) {x} (hx)`.

Also delete AnalyticMoments.lean:38-40 (`private lemma rvachev_continuous`) and add to the end of Differential.lean, immediately after `rvachev_contDiff` (line 260-262):

/-- Rvachev's function is continuous. -/
theorem rvachev_continuous (F : BoundedFabius) (hF : IsFabius F) :
    Continuous (rvachevUp F) :=
  (rvachev_contDiff F hF).continuous

The surviving AnalyticMoments declarations that call it — `rvachev_intervalIntegrable` (42-44), `pow_mul_rvachev_continuous` (47-49), and the uses at 128, 171, 529 — need no edit, since AnalyticMoments imports ...

**Verifier.** Every cited location checks out. AnalyticMoments.lean:23/28/33 declare `private lemma rvachev_eq_zero_of_le_neg_one`, `rvachev_eq_zero_of_one_le`, `rvachev_zero` inside `namespace Fabius` with binder structure `(F : BoundedFabius) (hF : IsFabius F) {x : ℝ} (hx : ...)`; Basic.lean:174/179/144 declare the public `rvachevUp_eq_zero_of_le_neg_one`, ...

#### `Odd (2 ^ e - 1)` is proved as a public theorem in Arithmetic.lean and again as a private lemma in Parity.lean, which imports it

Confidence high.  `Arithmetic.lean:141`, `Parity.lean:257`, `Parity.lean:281`, `Parity.lean:289`, `Arithmetic.lean:129`

**Why.** Parity.lean imports `FabiusFunction.Arithmetic` on line 1, so the identical public theorem is in scope; the private copy differs only in one bookkeeping step (`Nat.exists_eq_succ_of_ne_zero` + `pow_succ` instead of `Nat.even_pow`). The oddness facts for `oddFactorProduct` are the only ones of Arithmetic's five product definitions with no public oddness lemma, which is why Parity had to redo them privately.

**Proposal.** Delete the private `Fabius.odd_two_pow_sub_one` (Parity.lean:257-262) and use the already-imported public `Fabius.two_pow_sub_one_odd` (Arithmetic.lean:141) at its two call sites, Parity.lean:295 (`exact two_pow_sub_one_odd (by simp only [mem_Ico] at hj; omega)`) and Parity.lean:343 (`exact two_pow_sub_one_odd (binaryWeight_pos (n + 1) (by omega))`); both elaborate unchanged since the statements coincide.

Optionally, and separately, shorten the two neighbouring private product lemmas with the existing `finset_prod_odd` (Arithmetic.lean:129) instead of the hand-rolled `Finset.prod_induction` calls:
* Parity.lean:281 `odd_oddFactorProduct (a b : ℕ) : Odd (oddFactorProduct a b)` becomes `by unfold oddFactorProduct; exact finset_prod_odd _ _ (fun j _ => odd_two_mul_add_one j)` — mirroring `odd_oddDoubleFactorial` (Arithmetic.lean:147).
* Parity.lean:289 `odd_mersenne_product (a b : ℕ) (ha : 1 ≤ a) : Odd (∏ j ∈ Ico a b, (2 ^ (2 * j) - 1))` becomes `finset_prod_odd _ _ (fun j hj => two_pow_sub_one_odd (by simp only [mem_Ico] at hj; omega))`. Keep `ha : 1 ≤ a`: it is necessary, since at a ...

**Verifier.** The duplication is real and I confirmed it at every cited line. Arithmetic.lean:141 declares the public `theorem two_pow_sub_one_odd {e : ℕ} (he : 0 < e) : Odd (2 ^ e - 1)` in `namespace Fabius`; Parity.lean:257 declares `private lemma odd_two_pow_sub_one {w : ℕ} (hw : 0 < w) : Odd (2 ^ w - 1)` in the same namespace, and Parity.lean:1 is `import ...

### Cluster: discrete-limits-computability

#### `thueMorseSign_block_concat` and the two block-decomposition lemmas are verbatim triplicated across three modules

**DONE** in `affa557d2`.  `thueMorseSign_block_concat`, `sum_range_block_decomposition` and `sum_range_block_decomposition_with_remainder` are now public in `DyadicClosedForm.lean` with doc comments; the four copies in `FabiusUniformSpline` and `FabiusQBinomialFormula` are deleted and their call sites rewired.  Promotion and deletion had to be one commit: a private clone of a now-public name makes every reference inside its module ambiguous.  Not yet compiled.

Confidence high.  `DyadicClosedForm.lean:747`, `DyadicClosedForm.lean:774`, `DyadicClosedForm.lean:784`, `FabiusUniformSpline.lean:222`, `FabiusUniformSpline.lean:246`

**Why.** `thueMorseSign (h*2^k+r) = thueMorseSign h * thueMorseSign r` is the multiplicativity of the Thue–Morse sign under binary concatenation — the single structural fact behind every block-translation theorem in the corpus (`fabiusDyadic_block_translate`, `fabiusUniformSpline_block_translate`, the q-binomial prefix formula). Having it as three private copies means three separate inductions to maintain, and it is invisible to any downstream module that needs it. The two ...

**Proposal.** In DyadicClosedForm.lean, drop `private` from the three declarations at lines 747 (`thueMorseSign_block_concat`), 774 (`sum_range_block_decomposition`), and 784 (`sum_range_block_decomposition_with_remainder`), keeping the names and adding doc comments (e.g. for 747: multiplicativity of the Thue-Morse sign under binary concatenation, thueMorseSign (h * 2^k + r) = thueMorseSign h * thueMorseSign r for r < 2^k). This is safe: none of DyadicClosedForm's private defs appear in these signatures, and the declarations sit under a bare `namespace Fabius` with no enclosing section/variable block.

Then delete FabiusUniformSpline.lean lines 223 (NOT 222), 246, and 256 outright; the existing uses at lines 262, 337, 348, and 362 resolve unchanged to the now-public DyadicClosedForm names, and FabiusUniformSpline.lean:3 already has `import FabiusFunction.DyadicClosedForm`.

Then delete FabiusQBinomialFormula.lean lines 631 (`thueMorseSign_mul_pow_two_add`) and 660 (`sum_range_mul_blocks`) and rename their two call sites: `sum_range_mul_blocks` -> `sum_range_block_decomposition` at line 710, and ...

**Verifier.** Could not refute. All eight cited declarations exist with the quoted signatures (one line number is off by one: FabiusUniformSpline's thueMorseSign_block_concat is at 223, not 222). Textual diff of DyadicClosedForm.lean:747-772 against FabiusUniformSpline.lean:223-244 produces exactly two hunks, both the predicted one-line-vs-three-line `have hr' ...

#### `nat_pow_primrec` and `natPowPrimrec` are the same private theorem declared twice in one file

Confidence high.  `FabiusComputableSpline.lean:22`, `FabiusComputableSpline.lean:353`

**Why.** Identical statement, identical proof term, same file, same namespace, 331 lines apart. This is the clearest kind of duplicated content: one of the two is dead weight and the divergent naming convention (`nat_pow_primrec` vs `natPowPrimrec`) makes it easy for a future edit to fix one and not the other.

**Proposal.** Delete `natPowPrimrec` (FabiusComputableSpline.lean:353-354) and rewrite its two uses — line 372 (inside `clampDyadicNumeratorPR_primrec`, `natPowPrimrec.comp (Primrec.const 2) Primrec.snd`) and line 523 (inside `fabiusSplineApproxPR_primrec`, `natPowPrimrec.comp₂ (Primrec.const 2).to₂ Primrec₂.right`) — to use `nat_pow_primrec` instead. Purely internal to FabiusComputableSpline.lean; both declarations are `private`, no other module references either name, and no public API changes.

**Verifier.** Verified against source. Both declarations exist at the cited lines of Analysis/FabiusFunction/Lean/FabiusFunction/FabiusComputableSpline.lean and are byte-identical apart from the name: line 22 `private theorem nat_pow_primrec : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow` and line 353 the same with the name ...

#### The elementary identity `(n+1).choose 2 = n.choose 2 + n` is privately re-proved in six modules, with two further families of `choose 2` identities duplicated in pairs

**DONE** in `1ea3554f4`.  `choose_succ_two`, `two_mul_choose_two_add` and `choose_add_two_two` are now public in `Arithmetic.lean`; all ten private copies are deleted and all eighteen call sites rewired in that one commit.  `Arithmetic` compiles green at that SHA (`lake build +FabiusFunction.Arithmetic`, 1053 jobs, exit 0, no warnings).  Note that building `Arithmetic` alone does not exercise the rewired call sites, which live downstream; `FabiusDiscreteLimitComplexShift` (1 Fabius dependency), `DyadicAnalytic` (6) and `FabiusQBinomialTaylor` (43) between them cover all three lemmas.

Confidence high.  `DraftCounterexamples.lean:45`, `FabiusDiscreteLimitComplexShift.lean:201`, `FabiusDiscreteLimitToeplitz.lean:180`, `HalfQBinomial.lean:98`, `ThueMorseApproximation.lean:206`

**Why.** Eleven separate proofs of `Nat.choose_succ_succ` plus `simp [Nat.choose_one_right, add_comm]` is the single most repeated piece of mathematics in the corpus. The identity is used to normalize the `2 ^ (n choose 2)` prefactor that appears in essentially every Fabius formula, so it is genuinely central rather than incidental, and none of the eleven sites can reuse any other.

**Proposal.** Finding stands. Corrections to fold in.

(1) Line-number fixes for the inline sites: DyadicClosedForm.lean:45 and :58 (not :59); FabiusComputableSpline.lean:183 and :324 (not :184/:326); FabiusUniformSpline.lean:173 (not :174). The ten declaration sites are all exact.

(2) The site list under-counts. Three further inline re-proofs of the same one-line step were missed:
  - DyadicClosedForm.lean:584   have hchoose : (n + 2).choose 2 = (n + 1).choose 2 + (n + 1)
  - FabiusQBinomialFormula.lean:365   have htop : (n + 2).choose 2 = (n + 1).choose 2 + (n + 1)
  - HalfQBinomial.lean:110   have hchoose : (n + 2).choose 2 = (n + 1).choose 2 + (n + 1)  (this one already reuses the file-local choose_succ_two', so it only needs renaming)
So the true count is 6 private declarations of identity 1 plus 11 inline instances -- 17 sites, not 11. Note FabiusComputableSpline.lean:183 states the swapped form (p + 1) + (p + 1).choose 2, so its replacement needs `rw [choose_succ_two, Nat.add_comm]` rather than a bare rewrite.

(3) Every existing copy runs `rw [show n + 1 = Nat.succ n by omega, ...

**Verifier.** Every cited declaration exists at the stated line with the stated signature (verified all 11). The six identity-1 copies are byte-identical modulo binder letter and all are `private`, which in Lean 4 is module-scoped, so they genuinely cannot see one another. All three identities are true, including at the n=0 boundary where truncated subtraction ...

#### `integral_unitInterval_max_sub_mul_pow` is dead code duplicating `intervalIntegral_max_sub_mul_pow` in the same file

Confidence high.  `FabiusUniformSpline.lean:422`, `FabiusUniformSpline.lean:444`, `FabiusUniformSpline.lean:707`

**Why.** `rg` over the whole 174-module tree finds `integral_unitInterval_max_sub_mul_pow` only on its own declaration line — it is never used. Its proof is the proof of `intervalIntegral_max_sub_mul_pow` (the `intervalIntegral.integral_comp_sub_mul` step plus the same `intervalIntegral_max_pow` rewrite and `field_simp`) with a three-line subtype-to-interval preface glued on the front. The only user of the pair, `fabiusUniformPositiveSpline_smoothing` at line 707, calls the interval version.

**Proposal.** `integral_unitInterval_max_sub_mul_pow` is dead code duplicating `intervalIntegral_max_sub_mul_pow` in the same file. Corrected locations (worktree copy at FabiusUniformSpline.lean, 1426 lines): the dead lemma spans lines 381-401, the survivor spans 403-417, and the sole call site is line 666 inside `fabiusUniformPositiveSpline_smoothing` (declared 608). (The originally cited 422/444/707 are the line numbers of the separate checkout at C:\ProveIt\Analysis\FabiusFunction\Lean\FabiusFunction\FabiusUniformSpline.lean, which is 41 lines longer; do not apply a line-range delete without re-locating the declaration in the file actually being edited.)

Action: delete `integral_unitInterval_max_sub_mul_pow` entirely (worktree lines 381-401 plus the trailing blank line 402). Nothing references it anywhere in the tree, it is `private` and thus unreachable from other modules, and it carries no attribute. Deleting it leaves `integral_subtype` and `integral_Icc_eq_integral_Ioc` still used at lines 977 and 970 respectively, so no import becomes unused.

If a subtype-integral form is ever wanted, ...

**Verifier.** The substance holds up. In the designated source worktree file C:\ProveIt\.claude\worktrees\fabius-function-theorems-494024\Analysis\FabiusFunction\Lean\FabiusFunction\FabiusUniformSpline.lean, `integral_unitInterval_max_sub_mul_pow` (lines 381-401) has exactly the quoted signature, is `private`, carries no simp/other attribute, and its name ...

### Cluster: dyadic

#### `(n+2).choose 2 = (n+1).choose 2 + (n+1)` is proved inline fifteen times across nine modules

**DONE** in `1ea3554f4`.  `choose_succ_two`, `two_mul_choose_two_add` and `choose_add_two_two` are now public in `Arithmetic.lean`; all ten private copies are deleted and all eighteen call sites rewired in that one commit.  `Arithmetic` compiles green at that SHA (`lake build +FabiusFunction.Arithmetic`, 1053 jobs, exit 0, no warnings).  Note that building `Arithmetic` alone does not exercise the rewired call sites, which live downstream; `FabiusDiscreteLimitComplexShift` (1 Fabius dependency), `DyadicAnalytic` (6) and `FabiusQBinomialTaylor` (43) between them cover all three lemmas.

Confidence high.  `DyadicAnalytic.lean:60`, `DyadicClosedForm.lean:45`, `DyadicClosedForm.lean:58`, `DyadicClosedForm.lean:584`, `DyadicCorrectness.lean:113`

**Why.** Fifteen copies of a two-token arithmetic fact. Worse, DyadicClosedForm.lean already contains the strictly more general `choose_add_succ_two (m j) : (m + j + 1).choose 2 = (m + 1).choose 2 + m * j + (j + 1).choose 2` at line 36 — and its *own* proof re-derives the successor step inline at line 45, as does the neighbouring `two_mul_choose_succ_two` at line 58. The general lemma sitting three lines above was not used.

**Proposal.** Declare the fact ONCE, publicly, in Arithmetic.lean — not in DyadicClosedForm.lean. Arithmetic.lean has no FabiusFunction imports, already imports Mathlib.Data.Nat.Choose.Basic (so no new dependency is introduced), and is a transitive ancestor of all 22 modules that carry a copy, so a single declaration reaches every site with no risk of an import cycle.

State the base form, which is the one the seven existing private clones actually use, and derive the shifted form from it:

/-- Successor step of the triangular numbers: `C(n+1,2) = C(n,2) + n`. -/
theorem choose_succ_two (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  simpa [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ n 1

/-- Shifted form, used at most call sites: `C(n+2,2) = C(n+1,2) + (n+1)`. -/
theorem choose_succ_two_step (n : ℕ) :
    (n + 2).choose 2 = (n + 1).choose 2 + (n + 1) :=
  choose_succ_two (n + 1)

Then remove the copies, in three tiers:

TIER 1 - delete seven private clones and repoint their users:
  DyadicAnalytic.lean:60 choose_succ_two_step; HalfQBinomial.lean:98 choose_succ_two';
  ...

**Verifier.** The core duplication is real and verified, so I cannot refute it — but the finding is materially wrong in three places and its actionable recipe does not work as written.

WHAT SURVIVES. The statement (n+2).choose 2 = (n+1).choose 2 + (n+1) is true, including at the boundary n=0 (C(2,2)=1 = C(1,2)+1 = 0+1). All cited sites are the same fact over ...

#### Three pairs of theorems in `DyadicCorrectness` differ only by swapping `fabiusDyadicValue` for `extendedFabiusDyadicValue`

Confidence medium.  `DyadicCorrectness.lean:340`, `DyadicCorrectness.lean:352`, `DyadicCorrectness.lean:385`, `DyadicCorrectness.lean:398`, `DyadicCorrectness.lean:434`

**Why.** `fabiusDyadicValue_refine_iter` and `extendedFabiusDyadicValue_refine_iter` have literally the same eight-line induction with one identifier changed; likewise `..._eq_of_rat_eq` (nine lines each, both calling the same private `integer_eq_pow_mul_of_dyadic_eq`) and `evalFabiusDyadic_eq_none_iff` / `evalExtendedFabiusDyadic_eq_none_iff` (fourteen lines each). The generic content — 'any family `f : ℕ → ℤ → V` invariant under `(n, a) ↦ (n+1, 2a)` depends only on the represented rational' — is a ...

**Proposal.** Extract three private helpers in DyadicCorrectness.lean and keep all six public names as thin wrappers (names, argument order and arity unchanged). Drop the `{V : Type*}` generality — both value families are `ℕ → ℤ → ℚ` and both evaluators are `ℚ → Option ℚ`, so monomorphic helpers are simpler and dodge the universe binder under `set_option autoImplicit false`.

private theorem refine_iter_of_refine (f : ℕ → ℤ → ℚ)
    (hf : ∀ (n : ℕ) (a : ℤ), f (n + 1) (2 * a) = f n a) (n k : ℕ) (a : ℤ) :
    f (n + k) ((2 : ℤ) ^ k * a) = f n a

body = the existing lines 342-350 with `fabiusDyadicValue` replaced by `f` and `fabiusDyadicValue_refine (n + k)` replaced by `hf (n + k)`.

private theorem eq_of_rat_eq_of_refine_iter (f : ℕ → ℤ → ℚ)
    (hf : ∀ (n k : ℕ) (a : ℤ), f (n + k) ((2 : ℤ) ^ k * a) = f n a)
    (n m : ℕ) (a b : ℤ)
    (h : (a : ℚ) / (2 : ℚ) ^ n = (b : ℚ) / (2 : ℚ) ^ m) :
    f n a = f m b

body = the existing lines 386-395 with `integer_eq_pow_mul_of_dyadic_eq` (DyadicCorrectness.lean:365, NOT 372) unchanged and `fabiusDyadicValue_refine_iter` replaced by `hf`.

private theorem ...

**Verifier.** The finding survives every check I could throw at it.

(1) Existence/signatures. All six declarations exist in C:/ProveIt/.claude/worktrees/fabius-function-theorems-494024/Analysis/FabiusFunction/Lean/FabiusFunction/DyadicCorrectness.lean, with the quoted signatures verbatim. Theorem headers are at lines 340, 352, 383, 398, 435, 450; the cited ...

### Cluster: fourier-legendre

#### Four private helper lemmas are byte-identical copies between PeriodicRegularity.lean and PeriodicSmooth.lean

Confidence high.  `PeriodicRegularity.lean:86`, `PeriodicRegularity.lean:91`, `PeriodicRegularity.lean:185`, `PeriodicRegularity.lean:199`, `PeriodicSmooth.lean:65`

**Why.** This is verbatim copy-paste of proof text, not merely similar content: the tactic scripts of all four pairs agree character for character apart from the declaration name. The copies exist only because the originals were marked `private`, which is exactly the case the audit brief flags as private declarations with independent interest. Keeping two copies means any future fix to the dyadic-exponential calculus has to be made twice, in two modules that are already in an import relation.

**Proposal.** Deduplicate the four byte-identical private helpers by deleting the PeriodicSmooth.lean copies (forwardExp_hasDerivAt :65, forwardExp_ne_one :71, forwardExp_le :132, forwardDenominator_pos :140) and promoting the PeriodicRegularity.lean originals to public API. Home module: FabiusFunction.PeriodicRegularity, namespace Fabius.

Public forms (positivity retained exactly where it is decisive, dropped only where provably dead):

/-- The forward dyadic exponential never equals one at a positive scale. -/
theorem exp_neg_mul_two_pow_ne_one (s : ℝ) (hs : 0 < s) (n : ℕ) :
    Real.exp (-(s * (2 : ℝ) ^ n)) ≠ 1

/-- Derivative in the scale of the forward dyadic exponential. -/
theorem hasDerivAt_exp_neg_mul_two_pow (s : ℝ) (n : ℕ) :
    HasDerivAt (fun x : ℝ => Real.exp (-(x * (2 : ℝ) ^ n)))
      (-((2 : ℝ) ^ n) * Real.exp (-(s * (2 : ℝ) ^ n))) s

/-- Monotonicity of the forward dyadic exponential in the scale. -/
theorem exp_neg_mul_two_pow_le_of_le {a s : ℝ} (has : a ≤ s) (n : ℕ) :
    Real.exp (-(s * (2 : ℝ) ^ n)) ≤ Real.exp (-(a * (2 : ℝ) ^ n))

/-- The forward dyadic denominator is ...

**Verifier.** Could not refute; every check confirmed the finding. (1) All eight cited locations exist at the exact lines given with the exact quoted signatures: PeriodicRegularity.lean:86/91/185/199 and PeriodicSmooth.lean:65/71/132/140. (2) The "character for character" claim is literally true — I diffed each pair (statement lines after the declaration name ...

#### The substitution x = 2^t is proved from scratch four times

Confidence high.  `PeriodicMean.lean:24`, `PeriodicMean.lean:57`, `PeriodicFourier.lean:396`, `PeriodicFourier.lean:446`

**Why.** The four proofs are the same 25-40 line script: `let f := fun t => (2:ℝ)^t`, `let f' := fun t => Real.log 2 * (2:ℝ)^t`, `hf` by `(hasDerivAt_id t).const_rpow`, `hf'` by `continuous_const.mul (Real.continuous_const_rpow ..)`, `hg` by `.mono` onto the image, then `intervalIntegral.integral_comp_mul_deriv'` (real pair) / `intervalIntegral.integral_deriv_smul_comp'` (complex pair), then the same `rw [show (fun t => ...) = ... by funext t; unfold <kernel>; field_simp [hp]]` and ...

**Proposal.** Extract one vector-valued change-of-variables lemma into PeriodicMean.lean, immediately before line 24:

/-- Change of variables `x = 2^t` in an interval integral of any kernel that is
continuous on the positive half-line. -/
theorem intervalIntegral_smul_comp_two_rpow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ℝ → E) (hK : ContinuousOn K (Ioi (0 : ℝ))) (a b : ℝ) :
    (∫ t : ℝ in a..b, (Real.log 2 * (2 : ℝ) ^ t) • K ((2 : ℝ) ^ t)) =
      ∫ x : ℝ in (2 : ℝ) ^ a..(2 : ℝ) ^ b, K x

proved by `intervalIntegral.integral_deriv_smul_comp'` with `f := fun t => (2:ℝ)^t`, `f' := fun t => Real.log 2 * (2:ℝ)^t`, `g := K`, discharging the three side goals with `(hasDerivAt_id t).const_rpow`, `(continuous_const.mul (Real.continuous_const_rpow (by norm_num))).continuousOn`, and `hK.mono` via `Real.rpow_pos_of_pos`. No `CompleteSpace E` is required, and polymorphism in E keeps PeriodicMean free of any complex-analysis import while still serving the two ℂ-valued sites.

Also add the two pointwise bridges next to it — they are NOT `rfl`; both need the argument to be ...

**Verifier.** The finding survives every check I could aim at it.

(1) Signatures. All four cited declarations exist verbatim at the cited lines: `intervalIntegral_negativeLaplaceKernel_two_rpow` at PeriodicMean.lean:24, `intervalIntegral_boseLogKernel_two_rpow` at PeriodicMean.lean:57, `intervalIntegral_negativeLaplaceKernel_fourier` at ...

#### The dyadic-interval decomposition of an integral is proved twice, once per integrand

Confidence high.  `PeriodicMean.lean:166`, `PeriodicMean.lean:176`, `PeriodicFourier.lean:660`, `PeriodicFourier.lean:677`

**Why.** The proof bodies are identical modulo the integrand: both small versions are `hasSum_integral_iUnion (fun n => measurableSet_Ioc) pairwise_disjoint_smallDyadicInterval hf` followed by `simpa [iUnion_smallDyadicInterval]`; both large versions additionally do the same `IntegrableOn.congr_set_ae ... Ioi_ae_eq_Ici.symm`, `h.congr_fun (fun n => setIntegral_congr_set Ico_ae_eq_Ioc.symm)`, `rw [iUnion_largeDyadicInterval]`, `rw [setIntegral_congr_set Ioi_ae_eq_Ici]` dance. Nothing in the argument ...

**Proposal.** Add to PeriodicMean.lean, immediately after `pairwise_disjoint_largeDyadicInterval`:

/-- Any function integrable on `(0,1]` decomposes as an absolutely convergent sum
over the small dyadic intervals. -/
theorem hasSum_setIntegral_smallDyadicInterval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : IntegrableOn f (Ioc (0 : ℝ) 1)) :
    HasSum (fun n : ℕ => ∫ x : ℝ in smallDyadicInterval n, f x)
      (∫ x : ℝ in Ioc (0 : ℝ) 1, f x)

/-- Any function integrable on `(1,∞)` decomposes as an absolutely convergent sum
over the large dyadic intervals. -/
theorem hasSum_setIntegral_largeDyadicInterval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : IntegrableOn f (Ioi (1 : ℝ))) :
    HasSum (fun n : ℕ => ∫ x : ℝ in Ioc ((2 : ℝ) ^ n) ((2 : ℝ) ^ (n + 1)), f x)
      (∫ x : ℝ in Ioi (1 : ℝ), f x)

The four existing lemmas keep their names and become one-line applications with the integrability facts they already pass in (`integrableOn_boseFinitePartSmallKernel`, `integrableOn_boseFinitePartLargeKernel`, ...

**Verifier.** Verified and could not refute. (1) All four cited declarations exist at the cited lines with the quoted signatures (PeriodicMean.lean:166,176; PeriodicFourier.lean:660,677), and their proof bodies are identical modulo the integrand — the small pair is `hasSum_integral_iUnion (fun n => measurableSet_Ioc) pairwise_disjoint_smallDyadicInterval (...)` ...

#### complexSinc_neg and complexSinc_eq_cos_mul are each proved twice, the second time privately

Confidence high.  `WeakConvergence.lean:111`, `WeakConvergence.lean:122`, `PoissonSummation.lean:225`, `OriginalPaperSupplement.lean:81`

**Why.** These are literally the same two lemmas stated three times between them. Both duplicating modules already import FourierProduct directly (`PoissonSummation.lean:1`, `OriginalPaperSupplement.lean:4`), and `complexSinc` itself is defined far upstream in `Basic.lean:214`, so nothing forced the duplication except that neither author looked for an existing statement. Moving upstream cannot break any import path, since every module that can currently see `WeakConvergence.complexSinc_neg` also sees ...

**Proposal.** Move both facts into FourierProduct.lean (inside `namespace Fabius`, anywhere before `end Fabius` at :225 — they do not depend on `complexSinc_eq_dslope`), keeping the public names:

/-- The removable complex sinc function is even. -/
theorem complexSinc_neg (z : ℂ) : complexSinc (-z) = complexSinc z

/-- The half-angle factorization of the removable complex sinc function. -/
theorem complexSinc_eq_cos_mul (z : ℂ) :
    complexSinc z = Complex.cos (z / 2) * complexSinc (z / 2)

Then delete `complexSinc_neg_poisson` (PoissonSummation.lean:225) and `complexSinc_half` (OriginalPaperSupplement.lean:81) and rewrite their sole call sites (PoissonSummation.lean:242, OriginalPaperSupplement.lean:112) to the public names. WeakConvergence's own uses at :151 and :227 continue to resolve unchanged.

Two adjustments to the finding as written:

1. FourierProduct is imported at OriginalPaperSupplement.lean:3, not :4.

2. Do not copy the WeakConvergence proof of `complexSinc_neg` verbatim. Its one-line `simp [complexSinc, hz, Complex.sin_neg]` leans on the simp set of WeakConvergence's heavier ...

**Verifier.** Every cited declaration exists at the stated line with the stated signature, verbatim. WeakConvergence.lean:111 `complexSinc_eq_cos_mul` and OriginalPaperSupplement.lean:81 `complexSinc_half` have character-identical statements (`complexSinc z = Complex.cos (z / 2) * complexSinc (z / 2)`); WeakConvergence.lean:122 `complexSinc_neg` and ...

#### The support of rvachevUp is bounded four separate times; Basic.lean already has the strongest form

Confidence high.  `Basic.lean:194`, `Monotonicity.lean:220`, `FourierAnalytic.lean:27`, `FourierAnalytic.lean:286`

**Why.** `Function.support (rvachevUp F) ⊆ Icc (-1) 1` is stated twice under two different names in two modules, and the strictly stronger `⊆ Ioo (-1) 1` was already available in `Basic.lean` — which is in the import closure of every one of these modules (FourierAnalytic imports only `FabiusFunction.Basic` among project modules). The two FourierAnalytic proofs are the same nine-line `by_contra` / `rw [rvachevUp, if_pos ..]` / `hF.zero_of_nonpos` script written out twice, differing only in `≤` vs `<` in ...

**Proposal.** Scope the change to FourierAnalytic.lean only. (a) Replace the 11-line body at FourierAnalytic.lean:27 with `theorem rvachevUp_support_subset (F : BoundedFabius) (hF : IsFabius F) : Function.support (rvachevUp F) subset Icc (-1 : R) 1 := (support_rvachev_subset_Ioo F hF).trans Ioo_subset_Icc_self` — keep the Icc statement verbatim, since line 44 feeds it to `HasCompactSupport.of_support_subset_isCompact isCompact_Icc` and line 91 destructures it as `-1 <= t and t <= 1`. (b) Delete `private lemma up_support_subset_Ioc` (FourierAnalytic.lean:286-297) and at its sole use site (line 322) replace `apply up_support_subset_Ioc F hF` with `apply (support_rvachev_subset_Ioo F hF).trans Ioo_subset_Ioc_self`; the Ioc shape is required by `intervalIntegral.integral_eq_integral_of_support_subset`, so the composition must land in Ioc, not Ioo. (c) Leave Monotonicity.lean:220 unchanged — it is already a 2-line derivation from the exact equality `support_rvachevUp` (Monotonicity.lean:209) proved immediately above it, and rerouting it through Basic reduces nothing. Corrected rationale: ...

**Verifier.** Survives adversarial check. (1) All four declarations exist at the exact cited lines with exactly the quoted signatures (C:/ProveIt/.claude/worktrees/fabius-function-theorems-494024/Analysis/FabiusFunction/Lean/FabiusFunction/Basic.lean:194, Monotonicity.lean:220, FourierAnalytic.lean:27, FourierAnalytic.lean:286). (2) The duplication claim is ...

### Cluster: lambert-asymptotics

#### `remainder_eq_log_perturbation` is a byte-identical copy of a private lemma in a module it directly imports

Confidence high.  `FabiusLambertPhase.lean:170`, `FabiusLambertHigherExpansion.lean:25`

**Why.** I diffed the two proof bodies with `diff` and they are identical character for character (24 lines each; only the declaration name differs). FabiusLambertHigherExpansion.lean's first import line is `import FabiusFunction.FabiusLambertPhase`, so the copy exists purely because the original was marked `private`. The statement is a natural exact identity about two public definitions and has independent interest.

**Proposal.** Delete the 24-line `private lemma remainder_eq_log_perturbation` block at FabiusLambertHigherExpansion.lean:25-48, and in FabiusLambertPhase.lean:170 drop the `private` modifier from `dyadicLambertRemainder_eq_log_perturbation`, promoting it to a documented public theorem (a doc comment is required, not optional: AGENTS.md:37 mandates one on every non-`private` declaration):

/-- The Lambert displacement remainder is the logarithm of the relative
perturbation, rescaled by `log 2`. -/
theorem dyadicLambertRemainder_eq_log_perturbation {t : ℝ} (ht : 0 < t)
    (hsmall : Real.log 2 * (2 : ℝ) ^ (-t) < Real.exp (-1)) :
    dyadicLambertRemainder t =
      Real.log (1 + dyadicLambertPerturbation t) / Real.log 2

Home module is FabiusLambertPhase.lean, where both `dyadicLambertRemainder` (line 159) and `dyadicLambertPerturbation` (line 163) are defined. Correction to the finding's edit instructions: `secondRefined_eq` begins at FabiusLambertHigherExpansion.lean:50 (not 52), and its call at line 60 must be renamed from `remainder_eq_log_perturbation ht hsmall` to ...

**Verifier.** Confirmed on every axis. (1) Both cited declarations exist at exactly the cited lines with exactly the quoted signatures: FabiusLambertPhase.lean:170 `private lemma dyadicLambertRemainder_eq_log_perturbation`, FabiusLambertHigherExpansion.lean:25 `private lemma remainder_eq_log_perturbation`. (2) `diff` of lines 170-193 vs 25-48 reports exactly ...

#### Three verbatim copies of "bounded range ⇒ explicit nonnegative sup bound", all replaceable by one Mathlib call

Confidence high.  `PeriodicRegularity.lean:743`, `FabiusLambertDerivativeBounds.lean:57`, `FabiusLambertDerivativeBounds.lean:69`

**Why.** I diffed the three bodies: they are identical modulo the function name and the `isBounded_range_*` fact being unpacked; each is 11 lines of `Metric.isBounded_iff_subset_closedBall` plumbing. Mathlib already has `Bornology.IsBounded.exists_pos_norm_le : IsBounded s → ∃ R > 0, ∀ x ∈ s, ‖x‖ ≤ R` (Mathlib/Analysis/Normed/Group/Bounded.lean:81), which the author evidently did not know about — it collapses each proof to two lines. Each of the three `isBounded_range_*` inputs is itself produced by the ...

**Proposal.** The deduplication stands; two rationale claims need correction and one adjacent site should be mentioned.

(1) "Three verbatim copies" is slightly overstated: PeriodicRegularity.lean:743 differs cosmetically from the other two (`have hnorm` instead of `have this`, and `refine ⟨C, hC0, ?_⟩` + `intro t` instead of `refine ⟨C, hC0, fun t => ?_⟩`). The mathematical content and the tactic skeleton are identical, so the merge is still correct; the word should be "near-identical", not "verbatim".

(2) "which the author evidently did not know about" is false. The corpus already uses the sibling lemma `Bornology.IsBounded.exists_norm_le`, from the very same Mathlib file, at FabiusSaddleMassAllOrders.lean:69, :82, :345, :2100 and FabiusSaddleReferenceWeight.lean:361, :463. These three sites are stale older-style proofs, not evidence of an unknown API. Drop that clause.

(3) Add one generic lemma to PeriodicRegularity.lean, placed above line 743 (inside `namespace Fabius`, which is where it will land):

/-- A continuous periodic real function admits an explicit nonnegative
uniform bound. ...

**Verifier.** All three cited declarations exist at the stated lines with the stated signatures (PeriodicRegularity.lean:743 exists_bound_abs_secondDeriv_negativeLaplacePsi; FabiusLambertDerivativeBounds.lean:57 exists_bound_abs_deriv_negativeLaplacePsi; :69 exists_bound_abs_negativeLaplacePsiThird), and their proofs are the same 10-11 line ...

#### Three near-identical geometric-tail summations and three near-identical `|sᵏ · tail| ≤ C` bounds, differing only in an index and a constant

Confidence high.  `LaplacePeriodicSecondOrder.lean:81`, `FabiusLambertDerivativeBounds.lean:151`, `FabiusLambertDerivativeBounds.lean:222`, `FabiusLambertDerivativeBounds.lean:415`, `FabiusLambertDerivativeBounds.lean:429`

**Why.** `norm_negativeLaplaceForwardTailFirst_le_inv_sq` (LaplacePeriodicSecondOrder.lean:81), `..._Second_le_inv_cube` (FabiusLambertDerivativeBounds.lean:151) and `..._Third_le_inv_fourth` (FabiusLambertDerivativeBounds.lean:222) have identical 13-line bodies, differing only in `4/s^2 ↦ 24/s^3 ↦ 384/s^4` and the final `8/s^2 ↦ 48/s^3 ↦ 768/s^4`. Likewise `abs_mul_negativeLaplaceForwardTailFirst_le_eight` (:415), `abs_sq_mul_...Second_le` (:429) and `abs_cube_mul_...Third_le` (:444) have identical ...

**Proposal.** Finding stands. Add two generic helpers to PeriodicRegularity.lean (after the tail definitions at lines 376-388), with three refinements to the proposal as written:

(a) Drop the redundant `hC : 0 ≤ C` from the second helper — it is derivable, since `0 ≤ ‖y‖ ≤ C / s ^ (k+1)` with `0 < s ^ (k+1)` already forces `0 ≤ C`:

/-- A halving-geometric termwise bound gives summability and a `2K` tail bound. -/
theorem summable_and_norm_tsum_le_of_geometric_half {f : ℕ → ℝ} {K : ℝ}
    (h : ∀ n, ‖f n‖ ≤ K * (1 / 2 : ℝ) ^ n) :
    Summable f ∧ ‖∑' n, f n‖ ≤ 2 * K

/-- Scaling an inverse-power bound by `s ^ k` on `1 ≤ s` leaves the constant. -/
theorem abs_pow_mul_le_of_norm_le_div_pow {y C s : ℝ} (k : ℕ)
    (hs : 1 ≤ s) (h : ‖y‖ ≤ C / s ^ (k + 1)) :
    |s ^ k * y| ≤ C

(b) Prove the `2 * K` step with `tsum_geometric_two : ∑' n : ℕ, ((1:ℝ)/2) ^ n = 2` (Mathlib/Analysis/SpecificLimits/Basic.lean:342) after `tsum_mul_left`, rather than `tsum_geometric_of_norm_lt_one` + `ring` — one step shorter and it is the lemma that states exactly what is needed.

(c) Note the two call sites that need a ...

**Verifier.** The finding survives every attack. (1) All six declarations exist at the EXACT lines cited with the exact signatures quoted; the `current` snippet is a faithful (elided) transcription of LaplacePeriodicSecondOrder.lean:81 / FabiusLambertDerivativeBounds.lean:429. (2) The duplication is genuine and index-agnostic: all three tails are literally `∑' ...

#### `normalizedLaplaceMoment_two_eq_logDerivatives` is an unused exact duplicate of `normalizedLaplaceMoment_two_eq_logSecond_add_first_sq`

Confidence high.  `LaplaceCumulantAsymptotics.lean:42`, `EndpointLaplaceComparison.lean:828`

**Why.** The two statements are literally identical — same name-modulo-suffix, same binders `(F : BoundedFabius) (s : ℝ)`, same right-hand side, same implicit/explicit structure. `normalizedLaplaceMoment_two_eq_logDerivatives` is declared solely to give the `_two_` case a name matching `normalizedLaplaceMoment_three_eq_logDerivatives`/`_four_eq_logDerivatives`, and I grepped the whole 174-module directory: it is referenced nowhere. So the corpus carries two public API names for one theorem, one of them ...

**Proposal.** Delete lines 40-46 of C:\ProveIt\.claude\worktrees\fabius-function-theorems-494024\Analysis\FabiusFunction\Lean\FabiusFunction\LaplaceCumulantAsymptotics.lean — the docstring "The second normalized Laplace moment as a Bell polynomial in the first two logarithmic derivatives." (lines 40-41) together with the unused wrapper `lemma normalizedLaplaceMoment_two_eq_logDerivatives` (lines 42-46) and the trailing blank line. Change nothing else. Do NOT rename EndpointLaplaceComparison.lean:828 and do NOT introduce a compatibility wrapper: `normalizedLaplaceMoment_two_eq_logSecond_add_first_sq` keeps its existing name and its `unfold ...; ring` proof, and all three existing call sites (EndpointLaplaceComparison.lean:878, EndpointLaplaceComparison.lean:947, LaplaceMomentBounds.lean:351) already resolve to it, so no call site needs editing. This is the only edit that actually reduces the corpus from two public API names for this theorem to one. If a family-symmetric name is nonetheless wanted for readers, the corpus idiom is `alias normalizedLaplaceMoment_two_eq_logDerivatives := ...

**Verifier.** The factual core is fully confirmed, but the proposed remedy is defective and must be replaced. Confirmed: EndpointLaplaceComparison.lean:828 declares `normalizedLaplaceMoment_two_eq_logSecond_add_first_sq (F : BoundedFabius) (s : ℝ)` with the quoted RHS, proved by `unfold negativeLaplaceLogSecond negativeLaplaceLogFirst; ring`; ...

### Cluster: moments-probability

#### AnalyticMoments opens with private re-proofs of three theorems already public in Basic.lean

Confidence high.  `AnalyticMoments.lean:23`, `AnalyticMoments.lean:28`, `AnalyticMoments.lean:33`, `Basic.lean:144`, `Basic.lean:174`

**Why.** `AnalyticMoments.lean` imports `Differential`, which imports `Basic`, and already uses `Basic.norm_coe_rvachevUp_le_one` at lines 890 and 1026 — so the private copies are dead weight, not an import workaround. Two names for one fact also means downstream readers grep for the wrong one; `PaperStatements.lean:90` already exports a third alias `rvachev_zero := rvachevUp_zero F hF`, so `rvachevUp F 0 = 1` is currently proved or aliased three separate times in the corpus.

**Proposal.** Delete the three private lemmas at AnalyticMoments.lean:23-36 and rewrite the 16 (not 18) uses inside AnalyticMoments.lean to the Basic names. Exact tally, excluding the declaration lines: 10 uses of `rvachev_eq_zero_of_one_le` (lines 105, 124, 134, 165, 175, 563, 602, 746, 781, 975), 4 uses of `rvachev_eq_zero_of_le_neg_one` (lines 103, 747, 767, 973), 2 uses of `rvachev_zero` (lines 134, 602). Binder shapes are identical, so each is a pure rename: `rvachev_eq_zero_of_one_le F hF hx -> rvachevUp_eq_zero_of_one_le F hF hx`, `rvachev_eq_zero_of_le_neg_one F hF hx -> rvachevUp_eq_zero_of_le_neg_one F hF hx`, `rvachev_zero F hF -> rvachevUp_zero F hF`. Five endpoint applications collapse further to the Differential.lean names: the four occurrences of `rvachev_eq_zero_of_one_le F hF le_rfl` at lines 134, 175 (not 172), 602, and 746 (inside `rvachevLaplace_scaling`, which begins at line 704) become `rvachevUp_one F hF` (Differential.lean:32), and the occurrence of `rvachev_eq_zero_of_le_neg_one F hF le_rfl` at line 747 becomes `rvachevUp_neg_one F hF` (Differential.lean:36) — the ...

**Verifier.** Confirmed on every axis I could attack. (1) All seven cited locations exist exactly as quoted: AnalyticMoments.lean:23/28/33 are `private lemma`s declared immediately after `namespace Fabius` with no intervening `variable`/`section` binders, and Basic.lean:144/174/179 hold `rvachevUp_zero`, `rvachevUp_eq_zero_of_le_neg_one`, ...

#### `integral_rvachev_eq_one` and `integral_rvachevUp_eq_one` are two public names for the same theorem, each used exactly once

Confidence high.  `AnalyticMoments.lean:116`, `WeakConvergence.lean:44`

**Why.** The two statements are literally identical (`(F : BoundedFabius) (hF : IsFabius F) : (∫ x : ℝ, rvachevUp F x) = 1`), in the same namespace `Fabius`. Worse, the WeakConvergence version routes through `moment_eq_integral_formula F hF 0`, whose own `zero` branch (AnalyticMoments.lean:369) is discharged by `norm_num [momentIntegral, integral_rvachev_eq_one F hF]` — so the derivation is a round trip back to the theorem it duplicates.

**Proposal.** `Fabius.integral_rvachev_eq_one` (AnalyticMoments.lean:116-148) and `Fabius.integral_rvachevUp_eq_one` (WeakConvergence.lean:44-47) state the identical proposition in the identical namespace, and the WeakConvergence proof is circular in substance: it routes through `moment_eq_integral_formula F hF 0`, whose `zero` branch (AnalyticMoments.lean:369) is itself discharged by `integral_rvachev_eq_one F hF`. Each name has exactly one use corpus-wide (AnalyticMoments.lean:369 and WeakConvergence.lean:60 respectively).

Keep `integral_rvachev_eq_one` as the canonical statement — it carries the real FTC/substitution proof, it is upstream, and `rvachev_` is in fact this corpus's more common prefix (38 declarations vs 28 for `rvachevUp_`), including throughout AnalyticMoments itself. Then pick one of:

(a) Single name (removes the duplicate outright): delete `integral_rvachevUp_eq_one` from WeakConvergence.lean and change line 60 to
    rw [integral_rvachev_eq_one F hF]

(b) Explicit re-export (keeps the `rvachevUp_` spelling next to `rvachevUp_integrable` for downstream readers) — but then ...

**Verifier.** Survives verification on every axis. (1) Both declarations exist at the cited lines with the exact quoted signatures: AnalyticMoments.lean:116 and WeakConvergence.lean:44, both `(F : BoundedFabius) (hF : IsFabius F) : (∫ x : ℝ, rvachevUp F x) = 1`. (2) They are the same mathematical content, not a disguised variant: both are in `namespace Fabius`, ...

#### `coeff_halfMomentCandidatePS` re-proves 45 lines that are the `y = 1/2` case of `coeff_exp_mul_centeredMomentPowerSeries`

Confidence high.  `MomentPowerSeries.lean:213`, `MomentPowerSeries.lean:287`, `MomentPowerSeries.lean:343`, `MomentPowerSeries.lean:179`, `MomentPowerSeries.lean:267`

**Why.** `halfMomentCandidatePS` is *definitionally* `PowerSeries.rescale (1/2) (exp ℚ) * expandedMomentQuarter` and `centeredMomentPowerSeries` is *definitionally* `expandedMomentQuarter`, so the two lemmas are the same coefficient computation. The file already notices this once — `coeff_expHalf_mul_centeredMomentPowerSeries` (line 343) is proved by `simpa only [centeredMomentPowerSeries, halfMomentCandidatePS] using coeff_halfMomentCandidatePS n` — but derives the specialization from the special case ...

**Proposal.** Move the definition `centeredMomentPowerSeries` (MomentPowerSeries.lean:264-268, together with its docstring) and the theorem `coeff_exp_mul_centeredMomentPowerSeries` (lines 285-339) so that they sit AFTER `sum_range_even_div_two` (which ends at line 211) and BEFORE `coeff_halfMomentCandidatePS` (line 213). Do NOT move them above the definition `halfMomentCandidatePS` at line 179 as originally worded: `coeff_exp_mul_centeredMomentPowerSeries` rewrites with `sum_range_even_div_two` at line 322, so placing it before line 191 breaks the build. The `@[simp]` lemmas `coeff_centeredMomentPowerSeries_even` / `_odd` (lines 272, 279) may stay where they are or move with the definition; they cannot fire inside the general proof because its opening `rw` unfolds the constant immediately.

Then replace the 45-line body of `coeff_halfMomentCandidatePS` with a derivation from the general lemma:

private lemma coeff_halfMomentCandidatePS (n : ℕ) :
    PowerSeries.coeff n halfMomentCandidatePS =
      (∑ k ∈ range (n / 2 + 1), (Nat.choose n (2 * k) : ℚ) * moment k) /
        ((2 : ℚ) ^ n * ...

**Verifier.** The finding survives adversarial checking, with one correctable defect in the proposed edit.

CONFIRMED: (1) All five cited declarations exist at the exact cited lines with the signatures as quoted — no misquote that changes the math. (2) A mechanical diff of MomentPowerSeries.lean:218-262 against :295-339 reproduces the claimed result: 41 of 45 ...

#### `integral_pow_mul_rvachev_eq_interval` and `integral_rvachev_mul_eq_interval` are the same 27-line proof written twice

Confidence high.  `AnalyticMoments.lean:86`, `AnalyticMoments.lean:956`, `Basic.lean:194`

**Why.** Two 27-line proofs, one real-valued and one ℂ-valued, differ only in the integrand; the argument (indicator rewriting, `integral_Icc_eq_integral_Ioc`, `intervalIntegral.integral_of_le`) is about the support, not about Rvachev's function. The corpus already has `support_rvachev_subset_Ioo` in `Basic.lean`, so the support side condition is one line at each use site.

**Proposal.** Do NOT introduce a new helper lemma. Both `integral_pow_mul_rvachev_eq_interval` (AnalyticMoments.lean:86) and `integral_rvachev_mul_eq_interval` (AnalyticMoments.lean:956) should be collapsed onto the existing Mathlib lemma `intervalIntegral.integral_eq_integral_of_support_subset {a b} (h : Function.support f ⊆ Set.Ioc a b) : ∫ x in a..b, f x ∂μ = ∫ x, f x ∂μ` (Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1229), which is already used twice in this corpus for exactly this pattern — FabiusLegendreCoefficients.lean:107 and FourierAnalytic.lean:328 (the latter on a ℂ-valued integrand `p : ℝ → ℂ`, i.e. the same shape as `integral_rvachev_mul_eq_interval`).

Concretely, add ONE private support lemma in AnalyticMoments.lean (or reuse the Ioc-valued `up_support_subset_Ioc` pattern from FourierAnalytic.lean:286, or derive it from `Basic.support_rvachev_subset_Ioo` via `Set.Ioo_subset_Ioc_self`):

  private lemma rvachev_mul_support_subset_Ioc (F : BoundedFabius) (hF : IsFabius F)
      {E : Type*} [NormedAddCommGroup E] (h : ℝ → E) :
      Function.support (fun x => ??) ⊆ ...

**Verifier.** The duplication itself is confirmed and could not be refuted. Both cited declarations exist exactly as quoted (AnalyticMoments.lean:86 and :956), and after normalizing the integrand token in each, a diff of lines 86-113 against 956-983 reports ONLY the two signature lines as different — the 26-line proof bodies are byte-identical copy-paste ...

#### `independent_head_tail` and two `hhead` blocks inline verbatim copies of the public lemmas declared 500 lines later in the same file

Confidence high.  `ProbabilityRepresentation.lean:118`, `ProbabilityRepresentation.lean:151`, `ProbabilityRepresentation.lean:201`, `ProbabilityRepresentation.lean:418`, `ProbabilityRepresentation.lean:627`

**Why.** The file proves `uniformProduct.map (· 0) = volume` three times and mutual independence twice, while the corresponding public lemmas sit unused at the bottom of the file — they are advertised as "the prose proposition following Theorem 3" but never called. A reader auditing `uniformProduct_map_head_tail` cannot tell that the `hhead` step is the already-proved `coordinate_has_uniform_law`. Note the sibling `uniformProduct_map_tail` (line 112) is already a public lemma used exactly this way, so ...

**Proposal.** Move `independent_uniform_coordinates` (currently lines 625-630) and `coordinate_has_uniform_law` (lines 632-637) up to immediately after the `IsProbabilityMeasure uniformProduct` instance (after line 56), keeping their names, docstrings, statements and public status verbatim — both are referenced by fully qualified name in docs/PAPER_COVERAGE.md:25 and Paper05442.lean:25-26 as the Lean counterpart of the prose proposition following Theorem 3, so they must not be renamed or made private. Then: in `independent_head_tail` (line 118) replace the four-line `hi` block with `have hi := independent_uniform_coordinates`; in `uniformProduct_map_head_tail` (line 151) and `uniformProduct_map_head_tailSum` (line 201) replace each `hhead` block with `have hhead := coordinate_has_uniform_law 0`; in `weightedSumCDF_zero_of_nonpos` (line 418) replace `rw [uniformProduct, Measure.infinitePi_map_eval]` with `rw [coordinate_has_uniform_law]` (the index unifies to 0, matching the existing call style at FabiusUniformSpline.lean:946). Correction to the stated motivation: `coordinate_has_uniform_law` is ...

**Verifier.** Every citation checks out. Lines 120-122 are character-for-character the statement and proof of `independent_uniform_coordinates` (627-630); lines 151-154 and 201-204 are `coordinate_has_uniform_law` (633-637) at n := 0, and since the general-n proof is the identical two tactics (`unfold uniformProduct` / `rw [Measure.infinitePi_map_eval]`), ...

#### `momentDenominator_mul_tail` re-proves two public lemmas that are declared 30 lines below it in the same file

Confidence high.  `NormalizedEvenMoments.lean:28`, `NormalizedEvenMoments.lean:83`, `NormalizedEvenMoments.lean:89`

**Why.** `hmrs` is *character-for-character* `evenMersenneProduct_mul_interval k n hkn`, and `hodd` is `oddDoubleFactorial_mul_interval (k + 1) (n + 1) (Nat.succ_le_succ hkn)` after instantiating `a := k + 1`, `b := n + 1`. The public lemmas exist precisely to be used, but the only consumer in the file re-derives them; a future edit to either public lemma will silently leave the private copy stale.

**Proposal.** Move `oddDoubleFactorial_mul_interval` (currently lines 83-86) and `evenMersenneProduct_mul_interval` (currently lines 89-95), with their docstrings, to immediately after `evenMersenneProduct_eq_prod_Ico` (i.e. insert after line 26, before `momentDenominator_mul_tail` at line 28). This is dependency-safe: the first uses only Arithmetic.lean definitions plus Finset.prod_range_mul_prod_Ico, and the second uses only evenMersenneProduct_eq_prod_Ico (line 23) plus Finset.prod_Ico_consecutive. Then replace lines 33-45 of `momentDenominator_mul_tail` with:

  have hodd := oddDoubleFactorial_mul_interval (k + 1) (n + 1) (Nat.succ_le_succ hkn)
  have hmrs := evenMersenneProduct_mul_interval k n hkn

leaving `unfold momentDenominator` and the existing three-step calc (lines 46-56) untouched; the closing `rw [hodd, hmrs]` still applies since both hypotheses have exactly their former statements. Net -11 lines, no public signature changed. The exact call shape is already proven to elaborate at DenominatorBound.lean:36-38.

Two corrections to the finding's prose: the public lemmas are 55 lines ...

**Verifier.** Finding survives full adversarial check. (1) All three cited declarations exist at the cited lines with the quoted signatures: momentDenominator_mul_tail at NormalizedEvenMoments.lean:28 (spanning 28-56, 29 lines), oddDoubleFactorial_mul_interval at :83, evenMersenneProduct_mul_interval at :89. (2) The duplication is exact, not approximate: the ...

#### The triangular identity `(n+1).choose 2 = n.choose 2 + n` is proved from scratch in roughly twenty modules, eight of them as separate private lemmas

**DONE** in `1ea3554f4`.  `choose_succ_two`, `two_mul_choose_two_add` and `choose_add_two_two` are now public in `Arithmetic.lean`; all ten private copies are deleted and all eighteen call sites rewired in that one commit.  `Arithmetic` compiles green at that SHA (`lake build +FabiusFunction.Arithmetic`, 1053 jobs, exit 0, no warnings).  Note that building `Arithmetic` alone does not exercise the rewired call sites, which live downstream; `FabiusDiscreteLimitComplexShift` (1 Fabius dependency), `DyadicAnalytic` (6) and `FabiusQBinomialTaylor` (43) between them cover all three lemmas.

Confidence high.  `EarlyApproximants.lean:242`, `EarlyMeasureBridge.lean:126`, `StepApproximationLimit.lean:539`, `StepApproximationLimit.lean:700`, `MomentPowerSeries.lean:481`

**Why.** Thirteen verified locations (and about twenty in total by grep on `choose 2 = `) prove one arithmetic identity, five of them inside the moments/probability cluster and along a single import chain: `DyadicClosedForm → EarlyApproximants → EarlyMeasureBridge → StepMeasureBridge → StepApproximationLimit`, where it is re-derived at each of the five levels. This is the largest single-fact duplication I found in the corpus.

**Proposal.** Declare it once, public, in `Arithmetic.lean` — NOT `Basic.lean`, which nine of the consuming modules (MomentPowerSeries, DyadicClosedForm, DyadicCorrectness, EarlyApproximants, EarlyMeasureBridge, HalfQBinomial, ThueMorseGenerating, ThueMorsePrefix, FabiusDiscreteLimitComplexShift) do not import. Arithmetic.lean is the unique common ancestor and already imports Mathlib.Data.Nat.Choose.Basic (line 6), which supplies both ingredients.

/-- The triangular-number recurrence `C(n+1,2) = C(n,2) + n`. -/
theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  rw [show n + 1 = Nat.succ n by omega, Nat.choose_succ_succ]
  simp [Nat.choose_one_right, add_comm]

(Use this two-line proof, which is compiled verbatim at HalfQBinomial.lean:161-162 for this exact orientation, rather than the untested `simp [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]` one-liner; MomentPowerSeries:482 only demonstrates the one-liner for the reversed `n + n.choose 2` orientation.)

Then delete NINE private duplicates, not eight. The list must add ...

**Verifier.** The finding survives verification, but understates itself and misroutes the home module in one respect. Confirmed: every named private lemma exists with exactly the quoted signature (DraftCounterexamples.choose_succ_two:45, DyadicAnalytic.choose_succ_two_step:60, FabiusDiscreteLimitToeplitz.choose_succ_two_toeplitz:180, ...

### Cluster: negative-laplace

#### `x^k * exp(-x) ≤ k!` and `exp(-x)/(1-exp(-x))^m ≤ 2^m exp(-x)` are each proved 2–5 times, verbatim, because both are `private`

Confidence high.  `NegativeLaplaceDerivativeBounds.lean:115`, `NegativeLaplaceDerivativeBounds.lean:126`, `NegativeLaplaceDerivativeBounds.lean:133`, `FabiusLambertDerivativeBounds.lean:81`, `FabiusLambertDerivativeBounds.lean:91`

**Why.** `local_pow_mul_exp_neg_le_factorial` and `local_exp_neg_div_one_sub_pow_le` are byte-for-byte the same statements as the two `private` lemmas already available upstream (I confirmed by import-closure computation that `FabiusLambertDerivativeBounds` transitively imports `NegativeLaplaceDerivativeBounds` and `LaplaceMomentBounds`); the only reason they were re-typed is that the originals are `private`. Roughly 45 lines of proof text are pure copies, and the `k = 4` and `k = 2` instances are two ...

**Proposal.** Same refactor, with corrected coordinates and two mistakes fixed.

Corrected locations: NegativeLaplaceDerivativeBounds.lean:115 (`pow_mul_exp_neg_le_factorial`), :126 (`exp_neg_le_half`), :133 (`exp_neg_div_one_sub_pow_le`); FabiusLambertDerivativeBounds.lean:155 and :165 (the two `local_` copies), not 81/91; NegativeLaplaceVerticalFourthBound.lean:398 (`vertical_fourth_mul_exp_neg_le`), not 331; LaplaceMomentBounds.lean:118 (`pow_mul_exp_neg_quarter_le`, dead estimate at :127); LaplacePeriodicSecondOrder.lean:53-58 (inline `hpow`).

Move the three lemmas verbatim into `LaplaceMomentBounds.lean` (namespace `Fabius`, before `pow_mul_exp_neg_quarter_le` at line 118) and drop `private`. Verified: LaplaceMomentBounds is in the transitive import closure of all five client modules, none of them is in its closure (no cycle), and its direct import `Mathlib.Analysis.Complex.ExponentialBounds` supplies `Real.exp_neg_one_lt_half` while `Real.pow_div_factorial_le_exp` is already used at line 125.

Fixes to the original proposal:
- There are FOUR call sites in FabiusLambertDerivativeBounds, not ...

**Verifier.** The finding survives adversarial checking on substance; only its line numbers and one count are wrong. (1) Every cited declaration exists with the signature exactly as quoted. Three line numbers are stale: `local_pow_mul_exp_neg_le_factorial`/`local_exp_neg_div_one_sub_pow_le` are at FabiusLambertDerivativeBounds.lean:155/165 (not 81/91) and ...

#### The dyadic-iteration scaffold (`base on [1,2]` + `one increment per doubling` ⇒ `O(b)` at `r = 2^b`) is written out three times; the fourth-derivative version is literally the `m = 3` case of the all-order version

Confidence high.  `NegativeLaplaceVerticalFourthBound.lean:468`, `NegativeLaplaceVerticalFourthBound.lean:521`, `NegativeLaplaceVerticalFourthBound.lean:564`, `NegativeLaplaceVerticalAllOrderBound.lean:461`, `NegativeLaplaceVerticalAllOrderBound.lean:510`

**Why.** `exists_norm_iteratedDeriv_negativeLaplaceVerticalLog_le_dyadicScales` and `exists_norm_negativeLaplaceVerticalLogFourth_le_dyadicScales` have identical proof skeletons — same `bddAbove_def.mp (IsCompact.bddAbove_image …)` base extraction, same `induction k`, same `by_cases r ≤ 2`, same `let s := r / 2`, same `pow_succ`/`nlinarith` upper-bound step, same `norm_add_le` closing calc — differing only in the constant (`1542` vs `m! * 5 / (1/2)^m`) and in the function bounded. The same is true of ...

**Proposal.** Corrected line references: NegativeLaplaceVerticalFourthBound.lean:535 / :588 / :631; NegativeLaplaceVerticalAllOrderBound.lean:464 / :513 / :561; the `hinterval` induction at NegativeLaplaceDerivativeBounds.lean:355-395 inside `private theorem dyadic_recurrence_isBigO_nat` (:341); the identification lemma is `iteratedDeriv_negativeLaplaceVerticalLog_four` at NegativeLaplaceVerticalTaylor.lean:591.

Keep both abstract lemmas exactly as proposed; both are verified true and `NegativeLaplaceDerivativeBounds` is confirmed transitively upstream of both vertical modules with `Real.rpow` already available there:

  theorem norm_le_add_nsmul_of_dyadic_step
      {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) {A C : ℝ} (hC : 0 ≤ C)
      (hbase : ∀ {s : ℝ}, 1 ≤ s → s ≤ 2 → ‖f s‖ ≤ A)
      (hstep : ∀ {s : ℝ}, 1 ≤ s → ‖f (2 * s)‖ ≤ C + ‖f s‖)
      (m : ℕ) {s : ℝ} (hs : 1 ≤ s) (hsu : s ≤ (2 : ℝ) ^ (m + 1)) :
      ‖f s‖ ≤ A + (m + 1 : ℕ) * C

  theorem norm_le_mul_of_dyadic_step_rpow
      {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) {A C : ℝ}
      (hA : 0 ≤ A) (hC : 0 ≤ C)
      (h : ∀ (m ...

**Verifier.** All seven cited declarations exist with the signatures quoted verbatim (line numbers are stale — FourthBound is off by 67 due to commit 4c59369fe adding 70 lines of module docstring; actual lines are 535/588/631, 464/513/561, and hinterval at 355 inside dyadic_recurrence_isBigO_nat at 341). Both proposed abstract lemmas are mathematically true: I ...

#### `fabiusLaplaceMoment_zero_pos` and `generatingFunction_neg_pos` are the same theorem with the same two-line proof, in two sibling modules

Confidence high.  `NegativeLaplaceDerivatives.lean:30`, `NegativeLaplaceVertical.lean:451`, `NegativeLaplace.lean:410`

**Why.** `fabiusLaplaceMoment_zero` (LaplaceMoments.lean:119) is `rfl`, so the two statements are the same proposition, and both proofs invoke `exp_negativeLaplaceLog_eq_generatingFunction_neg` followed by `Real.exp_pos`. `NegativeLaplaceDerivatives` and `NegativeLaplaceVertical` are incomparable in the import graph (verified), which is why neither could use the other; the shared fact belongs in `NegativeLaplace.lean`, which is where the exponential representation is proved and which both transitively ...

**Proposal.** Hoist the shared positivity fact into NegativeLaplace.lean, immediately after exp_negativeLaplaceLog_eq_generatingFunction_neg (which ends around line 425), inside the existing `namespace Fabius`:

/-- The negative generating/Laplace transform is strictly positive at every
positive scale, because it is an exponential. -/
theorem generatingFunction_neg_pos
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) (hr : 0 < r) :
    0 < generatingFunction F (-r) := by
  rw [← exp_negativeLaplaceLog_eq_generatingFunction_neg F hF r hr]
  exact Real.exp_pos _

Then DELETE the declaration at NegativeLaplaceVertical.lean:451-455 outright — do NOT leave a one-line alias. Both modules are in `namespace Fabius` and NegativeLaplaceVertical transitively imports NegativeLaplace, so re-declaring the same name would fail with "'Fabius.generatingFunction_neg_pos' has already been declared". Deleting it is safe and requires no call-site edits: the identical fully-qualified name arrives through the import, so NegativeLaplaceVertical.lean:510 and :549, FabiusBromwichInput.lean:170, and ...

**Verifier.** The finding survives adversarial checking on all five axes. (1) Both declarations exist verbatim at the cited lines: NegativeLaplaceDerivatives.lean:30-35 and NegativeLaplaceVertical.lean:451-455, and the anchor lemma exp_negativeLaplaceLog_eq_generatingFunction_neg is at NegativeLaplace.lean:410-413 with exactly the quoted signature (F : ...

### Cluster: papers-aggregates

#### `support_rvachev_eq` and `rvachev_pos_of_mem_Ioo` are verbatim re-proofs of `support_rvachevUp` and `rvachevUp_pos_of_mem_Ioo` from the imported `Monotonicity`

Confidence high.  `Paper06487Supplement.lean:59`, `Paper06487Supplement.lean:91`, `Monotonicity.lean:200`, `Monotonicity.lean:209`

**Why.** These are not merely equivalent, they are character-for-character the same proposition in the same `Fabius` namespace, each proved from scratch. `Paper06487Supplement` imports `PaperStatements`, which imports `FabiusFunction.Monotonicity` directly (PaperStatements.lean:17), so the upstream versions are in scope. `Monotonicity.lean`'s own module header states that these order-theoretic facts were deliberately moved out of `PaperStatements` so consumers would not have to import the paper index; ...

**Proposal.** Title, corrected: `support_rvachev_eq` and `rvachev_pos_of_mem_Ioo` in `Paper06487Supplement` restate `support_rvachevUp` and `rvachevUp_pos_of_mem_Ioo` from the imported `Monotonicity` character-for-character, and prove them again independently (different tactic scripts, same content).

Action, unchanged in substance: keep `FabiusFunction.Monotonicity` as the home module and reduce the two supplement declarations to one-line forwards, retaining the public names and their doc comments as compatibility aliases:

`theorem rvachev_pos_of_mem_Ioo (F : BoundedFabius) (hF : IsFabius F) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : 0 < rvachevUp F x := rvachevUp_pos_of_mem_Ioo F hF hx`

`theorem support_rvachev_eq (F : BoundedFabius) (hF : IsFabius F) : Function.support (rvachevUp F) = Ioo (-1 : ℝ) 1 := support_rvachevUp F hF`

Both forwarders use `F`, `hF`, and `hx`, so no unused-binder warning is introduced, and the "doc comment on every non-private declaration" invariant is preserved.

One knock-on effect the finding did not state: lines 98 and 101 are the only uses in the entire tree of the ...

**Verifier.** Every load-bearing element of the claim checks out against the source.

(1) Locations and signatures are quoted accurately. `Paper06487Supplement.lean:59` is `theorem rvachev_pos_of_mem_Ioo (F : BoundedFabius) (hF : IsFabius F) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : 0 < rvachevUp F x`; `Monotonicity.lean:200` is `theorem rvachevUp_pos_of_mem_Ioo` ...

#### `(n + 1).choose 2 = n.choose 2 + n` is declared as a private lemma in three modules and re-derived inline in a dozen more; it is a one-line Mathlib consequence

**DONE** in `1ea3554f4`.  `choose_succ_two`, `two_mul_choose_two_add` and `choose_add_two_two` are now public in `Arithmetic.lean`; all ten private copies are deleted and all eighteen call sites rewired in that one commit.  `Arithmetic` compiles green at that SHA (`lake build +FabiusFunction.Arithmetic`, 1053 jobs, exit 0, no warnings).  Note that building `Arithmetic` alone does not exercise the rewired call sites, which live downstream; `FabiusDiscreteLimitComplexShift` (1 Fabius dependency), `DyadicAnalytic` (6) and `FabiusQBinomialTaylor` (43) between them cover all three lemmas.

Confidence high.  `DraftCounterexamples.lean:45`, `FabiusDiscreteLimitComplexShift.lean:201`, `FabiusDiscreteLimitToeplitz.lean:180`, `DyadicAnalytic.lean:60`, `DyadicClosedForm.lean:584`

**Why.** This exact identity is declared privately three times with near-identical proof bodies differing only in the bound-variable name, and re-derived as an anonymous `have` in at least ten further proofs (a shifted-index clone `choose_succ_two_step (j : ℕ) : (j + 2).choose 2 = (j + 1).choose 2 + (j + 1)` sits at DyadicAnalytic.lean:60, and `DyadicClosedForm.lean:584` re-proves it inside `two_mul_choose_succ_two` itself). It is the single most duplicated auxiliary fact in the corpus. It is also ...

**Proposal.** Add ONE public lemma to DyadicClosedForm.lean, immediately after the existing public `two_mul_choose_succ_two` (DyadicClosedForm.lean:61, not :53):

/-- Pascal's rule at `k = 2`.  Long-term home is `Arithmetic.lean`, which
already imports `Mathlib.Data.Nat.Choose.Basic`; it is landed here instead
because editing `Arithmetic.lean` invalidates all 176 modules
(see docs/COLLABORATION.md, "placement cost dominates placement purity"). -/
theorem choose_succ_two (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right, Nat.add_comm]

DyadicClosedForm imports Mathlib.Data.Nat.Choose.Sum, so Nat.choose_succ_succ' and Nat.choose_one_right are both in scope. If the `rw` chain needs a nudge on the `2` vs `1 + 1` literal, the corpus already has a working one-liner at FabiusQBinomialFormula.lean:905: `simp [Nat.choose_succ_succ, Nat.choose_one_right]`.

SCOPE OF THE CLEANUP -- only sites that already reach DyadicClosedForm (verified by transitive closure):
- Delete the private copies at DraftCounterexamples.lean:45, ...

**Verifier.** The duplication diagnosis is confirmed and is in fact UNDERSTATED, so I cannot refute it -- but the proposal as written is wrong in three checkable ways.

CONFIRMED. (a) The identity is true with no boundary failure: n=0 gives 1.choose 2 = 0 = 0.choose 2 + 0; n=1 gives 2.choose 2 = 1 = 1.choose 2 + 1. (b) Nat.choose_succ_succ' (n k) : (n+1).choose ...

### Cluster: regularity

#### `rvachev_pos_of_mem_Ioo` and `support_rvachev_eq` re-prove `Monotonicity.rvachevUp_pos_of_mem_Ioo` and `Monotonicity.support_rvachevUp` verbatim

Confidence high.  `Monotonicity.lean:200`, `Monotonicity.lean:209`, `Paper06487Supplement.lean:59`, `Paper06487Supplement.lean:91`

**Why.** Character-for-character identical signatures under two names, in two modules, with independently written proofs (`unfold rvachevUp; split_ifs` versus `rvachevUp_of_nonpos`/`rvachevUp_of_pos`). The `Monotonicity` module header states that these positivity and support facts were extracted *out of* `PaperStatements` precisely so consumers would not have to import the paper index — but the copies in `Paper06487Supplement` were never re-pointed at the extracted originals. Any future strengthening ...

**Proposal.** `Paper06487Supplement` imports `PaperStatements` (line 1), which imports `FabiusFunction.Monotonicity` (PaperStatements.lean:17), so both upstream theorems are already in scope. Replace the two bodies with one-line delegations, keeping the names for API compatibility:

theorem rvachev_pos_of_mem_Ioo (F : BoundedFabius) (hF : IsFabius F) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) : 0 < rvachevUp F x :=
  rvachevUp_pos_of_mem_Ioo F hF hx

theorem support_rvachev_eq (F : BoundedFabius) (hF : IsFabius F) :
    Function.support (rvachevUp F) = Ioo (-1 : ℝ) 1 :=
  support_rvachevUp F hF

(The downstream `rvachev_pos_iff_mem_Ioo` and `rvachevUp_eq_zero_iff_not_mem_Ioo`, Paper06487Supplement.lean:70 and :81, are genuinely new content and stay as they are.)

**Verifier.** Confirmed on every axis I could attack it. (1) All four cited declarations exist at the cited lines with the quoted signatures, character-identical binder lists and conclusions; no misquote. (2) The two pairs are genuinely the same mathematical content: same hypotheses (`BoundedFabius`, `IsFabius`, implicit `{x : ℝ}`, `hx : x ∈ Ioo (-1:ℝ) 1`), ...

#### `fabiusReal_le_two_mul_of_mem_Icc_half` is a 19-line private re-proof of `Regularity.fabiusReal_le_two_mul`

Confidence high.  `FabiusBinaryReductionSeries.lean:410`, `Regularity.lean:111`, `Regularity.lean:18`

**Why.** This is exactly the redundancy the `Regularity` module header claims to have already resolved: "The first removes the hypothesis `x ≤ 1/2` carried by an auxiliary estimate used elsewhere in the development." The auxiliary estimate is still there, still carrying `x ≤ 1/2`, and still re-deriving the mean-value bound from scratch. So this is simultaneously a duplication defect and a module-header claim that the corpus does not honour.

**Proposal.** Delete the 19-line private lemma at FabiusBinaryReductionSeries.lean:410-428 and replace its single use at line 458 with `fabiusReal_le_two_mul F hF htailHalf.1`, adding `import FabiusFunction.Regularity` at the top of FabiusBinaryReductionSeries.lean. Verified: this adds exactly one module to the file's transitive import closure (Regularity itself; `Mathlib.Analysis.Calculus.MeanValue` is already reachable there), and creates no cycle, since Regularity's project-side closure is {Arithmetic, Basic, Differential}, all already imported by FabiusBinaryReductionSeries. If the private name is kept for locality, make it the one-liner `private lemma fabiusReal_le_two_mul_of_mem_Icc_half (F : BoundedFabius) (hF : IsFabius F) (y : ℝ) (hy : y ∈ Icc (0 : ℝ) (1 / 2)) : fabiusReal F y ≤ 2 * y := fabiusReal_le_two_mul F hF hy.1`. Drop the finding's rationale clause about the Regularity module header being dishonoured: Regularity.lean:18-19 describes the auxiliary estimate as one "used elsewhere in the development", i.e. it acknowledges the duplicate rather than claiming to have removed it. The ...

**Verifier.** Every check passes. (1) Both declarations exist exactly as quoted: FabiusBinaryReductionSeries.lean:410-428 is a 19-line, docstring-free `private lemma fabiusReal_le_two_mul_of_mem_Icc_half ... (hy : y ∈ Icc (0:ℝ) (1/2)) : fabiusReal F y ≤ 2 * y` proved via `Convex.image_sub_le_mul_sub_of_deriv_le`; Regularity.lean:111 is `theorem ...

#### `Monotonicity.support_rvachev_subset` is a strictly weaker restatement of `Basic.support_rvachev_subset_Ioo`, and its name promises no interval

Confidence medium.  `Monotonicity.lean:220`, `Basic.lean:194`, `Monotonicity.lean:226`

**Why.** Three statements about the same support now coexist: `⊆ Ioo` (Basic, sharp, elementary), `= Ioo` (Monotonicity:209, sharpest), and `⊆ Icc` (Monotonicity:220, strictly weakest) — and the weakest one carries the unqualified name `support_rvachev_subset`, which reads as the canonical statement while being the least informative of the three. Its proof also routes through the strict-positivity machinery, which the `Ioo` version in `Basic` shows is unnecessary. The immediately following ...

**Proposal.** Delete `support_rvachev_subset` from Monotonicity.lean:219-223 AND update its sole consumer in the same commit. Grep confirms exactly one call site: FabiusLegendreCoefficients.lean:101, inside `integral_even_power_mul_rvachev_eq_moment`, currently

    have hmem := support_rvachev_subset F hF hup
    have hxne : x != -1 := by
      intro heq
      subst x
      exact hup (rvachevUp_eq_zero_of_le_neg_one F hF le_rfl)
    exact <lt_of_le_of_ne hmem.1 (Ne.symm hxne), hmem.2>

Replacing the Icc lemma with `Basic.support_rvachev_subset_Ioo` collapses this to

    have hmem := support_rvachev_subset_Ioo F hF hup
    exact <hmem.1, hmem.2.le>

which drops the `hxne` endpoint detour and the `rvachevUp_eq_zero_of_le_neg_one` appeal entirely, so the deletion strictly shortens the corpus rather than merely relocating work.

If instead the `Icc` form must be retained for compatibility, rename it to `support_rvachev_subset_Icc`, keep it adjacent to `support_rvachevUp`, prove it as

    theorem support_rvachev_subset_Icc (F : BoundedFabius) (hF : IsFabius F) :
        Function.support (rvachevUp ...

**Verifier.** Verified against the files. (1) Both declarations exist verbatim at the cited lines, in the same namespace `Fabius`, with identical hypotheses `(F : BoundedFabius) (hF : IsFabius F)` — no hypothesis, type, or index difference to hide behind; `Icc` is strictly weaker than `Ioo` here. (2) The replacement proof is valid: `Ioo_subset_Icc_self` is real ...

### Cluster: saddle

#### The order-indexed central-radius API duplicates the unindexed one five times over; `fabiusSaddleCentralRadiusOrder 0 = fabiusSaddleCentralRadius` is never stated

Confidence high.  `FabiusSaddleTail.lean:587`, `FabiusSaddleTail.lean:590`, `FabiusSaddleTail.lean:595`, `FabiusSaddleTail.lean:601`, `FabiusSaddleTail.lean:495`

**Why.** Five lemma pairs are the same mathematics at `N = 0` and `N` general, with essentially transcribed proofs. `standardized_intermediate_tail_le_inv` (56 lines) and `ordered_intermediate_tail_le_inv_pow` (72 lines) share the same `lam`, `hlam_lower`, `hcoeff : 2 / lam ≤ 16`, `hexp`, `hpow` skeleton and differ only by the factor `(N + 1)` inside `hA_sq` and the exponent on `b⁻¹`. `standardized_intermediate_tail_le_inv` is used only twice, both inside `FabiusSaddleTail.lean` (lines 629 and 680), so ...

**Proposal.** Scope the finding to the FOUR genuine duplicates in FabiusSaddleTailAllOrders.lean and drop the private-lemma pair entirely.

Corrected locations: FabiusSaddleTail.lean:495, 587, 590, 595, 601 (correct as cited) and FabiusSaddleTailAllOrders.lean:56, 59, 65, 73, 85 (NOT 12/15/21/29/41 — those are docstring lines).

Corrected proposal: move `fabiusSaddleCentralRadiusOrder` (AllOrders:56) together with `fabiusSaddleCentralRadiusOrder_pos` (:59), `sq_fabiusSaddleCentralRadiusOrder` (:65), `one_le_fabiusSaddleCentralRadiusOrder` (:73) and `ordered_intermediate_tail_le_inv_pow` (:85) up into `FabiusSaddleTail.lean` (namespace `Fabius`, which both files share). They need nothing beyond `FabiusSaddleTail`'s existing imports, and `FabiusSaddleTailAllOrders` imports `FabiusSaddleTail`, so every downstream reference in FabiusSaddleCentralRadiusAsymptotics.lean, FabiusSaddleMassAllOrders.lean and GaussianPolynomialTailAllOrders.lean still resolves. Then add

/-- The order-zero central radius is the standardized radius `√(32 log b)`. -/
@[simp] theorem fabiusSaddleCentralRadiusOrder_zero (b : ...

**Verifier.** The core duplication claim is confirmed for FOUR of the five pairs, but the fifth is structurally impossible and the citations are substantially wrong.

CONFIRMED: `fabiusSaddleCentralRadius` (FabiusSaddleTail.lean:587) and its `_pos`/`sq_`/`one_le_` lemmas (590/595/601), plus `standardized_intermediate_tail_le_inv` (495), are exactly the N=0 ...

#### Three private helper declarations are copied verbatim (with a prime) into a module that already imports the originals

Confidence high.  `FabiusSaddleExpansionCoefficients.lean:81`, `FabiusSaddleExpansionCoefficients.lean:87`, `FabiusSaddleExpansionCoefficients.lean:100`, `FabiusSaddleReferenceWeight.lean:106`, `FabiusSaddleReferenceWeight.lean:112`

**Why.** `FabiusSaddleReferenceWeight.lean` imports `FabiusSaddleExpansionCoefficients` on line 1, so the copies exist purely because the originals are `private`. I diffed lines 81-115 of the first file against lines 106-140 of the second after stripping the primes: they are identical. Two definitions of the same continuous-map lift means any future change to the exponent polynomial has to be mirrored in two places, and the two `Polynomial C(ℝ, ℂ)` families are not definitionally linked, so `expCoeff` ...

**Proposal.** Delete the three primed copies at FabiusSaddleReferenceWeight.lean:105-138 (`negativeLaplaceBoundedExponentJetContinuousMap'`, `negativeLaplaceExponentPolynomialContinuous'`, `negativeLaplaceExponentPolynomialContinuous'_map`). Remove the `private` modifier from the three originals at FabiusSaddleExpansionCoefficients.lean:80, :86, :99 and give each a doc comment; do NOT add an explicit `noncomputable` keyword, since all three already sit inside the `noncomputable section` opened at line 33.

/-- The bounded exponent jet of order `n`, packaged as a continuous map `ℝ → ℂ`. -/
def negativeLaplaceBoundedExponentJetContinuousMap (n : ℕ) : C(ℝ, ℂ)

/-- The order-`m` exponent polynomial lifted to coefficients in `C(ℝ, ℂ)`. -/
def negativeLaplaceExponentPolynomialContinuous (m : ℕ) : Polynomial C(ℝ, ℂ)

/-- Evaluating the continuous-coefficient exponent polynomial at `t` recovers
`negativeLaplaceExponentPolynomial m t`. -/
theorem negativeLaplaceExponentPolynomialContinuous_map (m : ℕ) (t : ℝ) : …

Then in FabiusSaddleReferenceWeight.lean rename every primed occurrence to the unprimed name ...

**Verifier.** The core deduplication claim is confirmed by direct textual diff and cannot be refuted. (1) All six cited line numbers land exactly on the signature lines of real declarations: FabiusSaddleExpansionCoefficients.lean 80/81, 86/87, 99/100 and FabiusSaddleReferenceWeight.lean 105/106, 111/112, 124/125. Signatures are quoted accurately. (2) I ...

#### Gaussian polynomial-moment integrability is proved five times across the cluster

Confidence high.  `GaussianPolynomialContraction.lean:29`, `GaussianPolynomialContraction.lean:43`, `FabiusSaddleCentral.lean:41`, `FabiusSaddleReferenceTail.lean:34`, `FabiusSaddleMassAllOrders.lean:281`

**Why.** The same integrability fact is currently proved by `integrable_rpow_mul_exp_neg_mul_sq (b := 1/2) (s := n)` in two modules and re-derived by `.norm.congr` in four more places. The three `FabiusSaddleMassAllOrders` copies are the most clearly avoidable: that module already imports `GaussianPolynomialContraction` (via `GaussianPolynomialWholeIntegral`) and already refers to `integrable_realGaussian_mul_pow` unqualified on the very same lines, so `integrable_realGaussian_mul_abs_pow d` is in scope ...

**Proposal.** Split the fix into a free part and a rebuild-costly part, and correct the citations.

CITATIONS: the two misquoted locations are `FabiusSaddleCentral.lean:111` (not 41) and `FabiusSaddleReferenceTail.lean:98` (not 34). Honest count: the signed statement `Integrable (fun v => exp (-(v^2)/2) * v^n)` is proved twice (GaussianPolynomialContraction.lean:29, FabiusSaddleCentral.lean:111); the absolute statement `... * |v|^n` is proved five times (GaussianPolynomialContraction.lean:43, FabiusSaddleReferenceTail.lean:98, FabiusSaddleMassAllOrders.lean:281, 1085, 1199).

PART 1 (do this unconditionally; zero import change, rebuilds one module). In `FabiusSaddleMassAllOrders.lean` replace the three blocks with the existing lemma, which is already in scope via `open SaddleExpansion` (line 25) and the transitive import of `GaussianPolynomialContraction` through `GaussianPolynomialWholeIntegral`:
- line 1085 and line 1199: `have hg : Integrable (fun v : ℝ => Real.exp (-(v ^ 2) / 2) * |v| ^ d) := integrable_realGaussian_mul_abs_pow d` (and `have hgaussAbs (d : ℕ) : ... := ...

**Verifier.** The finding holds on substance; only its bookkeeping is sloppy. All seven declarations exist with the quoted signatures, but two line numbers are wrong: `FabiusSaddleCentral.integrable_gaussian_mul_pow` is at line 111, not 41, and `FabiusSaddleReferenceTail.integrable_gaussian_abs_pow` is at line 98, not 34 (both cited lines fall inside module ...

#### "Bounded range composed with anything is O(1)" is written out four times verbatim

Confidence high.  `FabiusSaddleReferenceWeight.lean:359`, `FabiusSaddleReferenceWeight.lean:461`, `FabiusSaddleMassAllOrders.lean:340`, `FabiusSaddleMassAllOrders.lean:2098`

**Why.** Four independent copies of the same three-tactic argument, each attached to a different bounded-range lemma from the periodicity API (`isBounded_range_negativeLaplaceExpCoeff_coeff`, `isBounded_range_negativeLaplaceFiniteExpQuotient_coeff_coeff`, `isBounded_range_negativeLaplaceBoundedExponentJet`, `isBounded_range_fabiusSaddleMassCoefficient`). This is the standard bridge from the corpus's `Function.Periodic.isBounded_of_continuous` regularity results to its `IsBigO` asymptotics, and it ...

**Proposal.** Add to SaddleExpansionAlgebra.lean (namespace `Fabius.SaddleExpansion`, which both cited files already `open`), with the target constant generalized so a single lemma serves the `(1 : ℝ)` and `(1 : ℂ)` targets without an `ofReal` bridge:

/-- A function with bounded range is `O(1)` after precomposition with any map,
along any filter. -/
theorem isBigO_one_of_isBounded_range
    {α β ℰ 𝕜 : Type*} [SeminormedAddGroup ℰ]
    [SeminormedAddGroup 𝕜] [One 𝕜] [NormOneClass 𝕜] {l : Filter α}
    (g : β → ℰ) (hg : Bornology.IsBounded (Set.range g)) (u : α → β) :
    (fun i => g (u i)) =O[l] (fun _i => (1 : 𝕜)) := by
  obtain ⟨C, hC⟩ := hg.exists_norm_le
  exact IsBigO.of_bound C (by
    filter_upwards with i
    simpa using hC _ ⟨u i, rfl⟩)

(`[NormedDivisionRing 𝕜]` is an acceptable simpler bound; ℝ and ℂ both qualify either way. Not compiled — this audit was read-only.)

Site instantiations, which are NOT uniform (the finding's "verbatim" is wrong):
- FabiusSaddleReferenceWeight.lean:355 (target `(1 : ℂ)`, ℂ-valued): `isBigO_one_of_isBounded_range (𝕜 := ℂ) _ ...

**Verifier.** All four cited sites exist and do repeat the same three-tactic bridge (`.exists_norm_le` → `IsBigO.of_bound C` → `filter_upwards` → `simpa … hC _ ⟨u i, rfl⟩`): FabiusSaddleReferenceWeight.lean:355-364 and :457-466 (both `private theorem`, signatures quoted accurately), FabiusSaddleMassAllOrders.lean:340-348, and the first bullet of ...

#### The value of the Fabius function at `2⁻ᵐ` in halfMoment normalization is proved twice, once publicly and once privately in another module

Confidence medium.  `TaylorReduction.lean:84`, `AnalyticMoments.lean:451`, `DyadicAnalytic.lean:443`

**Why.** Cross-cluster duplication: both proofs run the identical chain `fabiusDyadic_cast F hF n 1 Nat.one_le_two_pow` → `fabiusAtInverseTwoPow_eq_halfMoment` → `halfMomentFabiusValue` → `push_cast`. Neither module imports the other (`TaylorReduction`'s closure is 9 modules and does not contain `AnalyticMoments`), so the second author simply redid the derivation. The identity is also the natural companion to the already-public `extendedFabius_inverse_two_pow_eq_sum_compositions` ...

**Proposal.** Hoist the shared value identity into DyadicAnalytic.lean (after fabiusDyadic_cast at line 443), which is the deepest common ancestor of TaylorReduction (9-module closure) and AnalyticMoments (7-module closure) and needs no new imports:

/-- Exact value of the Fabius function at an inverse power of two, in the
half-moment normalization of equation (22). -/
theorem fabiusReal_inverse_two_pow_eq_halfMoment
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    fabiusReal F (((2 : ℝ) ^ n)⁻¹) =
      (halfMoment n : ℝ) / ((n.factorial : ℝ) * (2 : ℝ) ^ n.choose 2)

Its proof does not need to repeat the fabiusDyadic_cast chain: DyadicAnalytic.lean:287 already proves the private `analyticInverseValue_eq_fabiusAtInverseTwoPow : analyticInverseValue F n = (fabiusAtInverseTwoPow n : ℝ)`, whose LHS unfolds (via inverseTwoPowReal, line 24) to `fabiusReal F ((2 : ℝ) ^ n)⁻¹`, so the new theorem follows by that lemma plus `fabiusAtInverseTwoPow_eq_halfMoment` (MomentPowerSeries.lean:474), `halfMomentFabiusValue` (Arithmetic.lean:360) and `push_cast`.

Then:
- ...

**Verifier.** All three citations check out exactly: TaylorReduction.lean:84 is `private theorem extendedFabius_inverse_two_pow` with the quoted signature, AnalyticMoments.lean:451 is `theorem halfMoment_eq_fabius_formula` with the quoted signature, and DyadicAnalytic.lean:443 is `fabiusDyadic_cast`. I computed the import closures: TaylorReduction's closure is ...

#### `log b ^ n / b → 0` is proved as a private lemma in two different modules

Confidence medium.  `FabiusSaddleCentralLambert.lean:367`, `FabiusSaddleCentralRadiusAsymptotics.lean:18`

**Why.** Both are private one-line consequences of the same Mathlib lemma `Real.isLittleO_pow_log_id_atTop`, and the constant-multiple version is nothing but `.const_mul C` on the other. `FabiusSaddleCentralLambert` calls its copy five times (lines 377, 379, 404, 406, 428) with an explicit `.const_mul`, i.e. it reconstructs the second lemma inline every time. Since both are private, unifying them is purely additive and breaks no public name or import path.

**Proposal.** Corrected line citations: the Lambert copy is at FabiusSaddleCentralLambert.lean:451 (the cited 367 is three commits stale), with its five call sites at lines 461, 463, 488, 490 and 512. The second copy is at FabiusSaddleCentralRadiusAsymptotics.lean:18, used once, at line 30.

Action, otherwise unchanged: delete both private copies and add a single public lemma to FabiusSaddleTail.lean, inside the existing `namespace Fabius` (which already carries `open Filter Set MeasureTheory Asymptotics` and `open scoped Topology`), placed next to `fabiusSaddleCentralRadius` / `sq_fabiusSaddleCentralRadius` at lines 587-595 — its topical home, since all five Lambert consumers rewrite through `sq_fabiusSaddleCentralRadius`. FabiusSaddleTail is a common ancestor of both sites, not the "deepest" module in their closures (NegativeLaplaceVertical and its own ancestors are deeper); it is chosen for topicality.

/-- Powers of `log b` are negligible against `b`. -/
theorem tendsto_log_pow_div_id_atTop (n : ℕ) :
    Tendsto (fun b : ℝ => Real.log b ^ n / b) atTop (nhds 0) :=
  ...

**Verifier.** The finding survives all five adversarial checks; only its line citations are stale.

(1) EXISTENCE/SIGNATURE. Both declarations exist with the signatures quoted verbatim. `tendsto_log_pow_div_id_atTop` is at FabiusSaddleCentralLambert.lean:451, not 367; `git show HEAD~3:...` places it at exactly 367, so the audit ran three commits back, before ...

### Cluster: thuemorse-qbinomial

#### `fabiusReal_le_two_mul_of_mem_Icc_half` re-proves the already-public `Regularity.fabiusReal_le_two_mul`, in a weaker form, with a 20-line mean-value argument

Confidence high.  `FabiusBinaryReductionSeries.lean:410`, `Regularity.lean:111`

**Why.** The exact statement, with a weaker hypothesis (`0 ≤ x` instead of `x ∈ Icc 0 (1/2)`), already exists as a public theorem, and its docstring even spells out the case split the private copy avoids: "dominated by `2x` on the whole half line `[0, ∞)`. On `[1/2, ∞)` this is the trivial bound `F ≤ 1 ≤ 2x`". The private copy costs a `Convex.image_sub_le_mul_sub_of_deriv_le` argument plus two support lemmas that exist only to feed it.

**Proposal.** Delete only `fabiusReal_le_two_mul_of_mem_Icc_half` (FabiusBinaryReductionSeries.lean:410-428). Add `import FabiusFunction.Regularity` to FabiusBinaryReductionSeries.lean (safe: Regularity's FabiusFunction closure is exactly {Arithmetic, Basic, Differential}, already a subset of this module's closure; no cycle, no new Mathlib weight). At the single use site (line 458) replace `fabiusReal_le_two_mul_of_mem_Icc_half F hF _ htailHalf` with `fabiusReal_le_two_mul F hF htailHalf.1`. KEEP `binaryTail_mem_Icc_half` (:438) and `inverse_two_pow_le_half` (:430): `binaryTail_mem_Icc_half` is independently needed at line 449 to build `htailUnit : binaryTail x N ∈ Icc (0:ℝ) 1` for `extendedFabius_eq_fabiusReal`, and it is what keeps the `hN : 1 ≤ N` hypothesis of the public `norm_binaryReductionRemainder_le` used. (If one insists on removing them too, lines 449-451 must be rewritten as `have htailUnit : binaryTail x N ∈ Icc (0:ℝ) 1 := ⟨binaryTail_nonneg x N hx0, (binaryTail_lt x N).le.trans (by positivity-style proof of ((2:ℝ)^N)⁻¹ ≤ 1)⟩`, and `hN` must be renamed `_hN` or dropped from the ...

**Verifier.** The core of the finding survives every check. Both declarations exist at the cited lines with the quoted signatures: FabiusBinaryReductionSeries.lean:410 has `private lemma fabiusReal_le_two_mul_of_mem_Icc_half (F) (hF) (y : ℝ) (hy : y ∈ Icc 0 (1/2)) : fabiusReal F y ≤ 2 * y` proved over 20 lines via `Convex.image_sub_le_mul_sub_of_deriv_le`, and ...

#### `(n+1).choose 2 = n.choose 2 + n` and its two algebraic restatements are re-proved privately five times in this cluster (about twenty times corpus-wide), although a public lemma in `DyadicClosedForm` already yields it

**DONE** in `1ea3554f4`.  `choose_succ_two`, `two_mul_choose_two_add` and `choose_add_two_two` are now public in `Arithmetic.lean`; all ten private copies are deleted and all eighteen call sites rewired in that one commit.  `Arithmetic` compiles green at that SHA (`lake build +FabiusFunction.Arithmetic`, 1053 jobs, exit 0, no warnings).  Note that building `Arithmetic` alone does not exercise the rewired call sites, which live downstream; `FabiusDiscreteLimitComplexShift` (1 Fabius dependency), `DyadicAnalytic` (6) and `FabiusQBinomialTaylor` (43) between them cover all three lemmas.

Confidence high.  `ThueMorseApproximation.lean:206`, `ThueMorseGenerating.lean:135`, `HalfQBinomial.lean:98`, `HalfQBinomial.lean:116`, `ThueMorseExponential.lean:468`

**Why.** `square_eq_choose_sum` (HalfQBinomial.lean:116) and `choose_square_split` (FabiusQBinomialFormula.lean:360) are the identical statement with the identical induction proof, and FabiusQBinomialFormula.lean imports HalfQBinomial.lean directly — the second copy exists only because the first is `private`. The successor identity is additionally proved inline inside `choose_add_succ_two` and `two_mul_choose_succ_two` themselves (DyadicClosedForm.lean:44 and :62), so the canonical module already ...

**Proposal.** In DyadicClosedForm.lean, next to `choose_add_succ_two` (line 36) and `two_mul_choose_succ_two` (line 53), add two public lemmas:

  lemma choose_succ_two (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n
  lemma mul_self_eq_choose_succ_two_add_choose_two (n : ℕ) : n * n = (n + 1).choose 2 + n.choose 2

Prove the first by `cases n` plus `choose_add_succ_two 1 n` (which gives `(n + 2).choose 2 = (n + 1).choose 2 + (n + 1)` after `Nat.choose_self`), or keep the existing three-line `Nat.choose_succ_succ` script once. Prove the second by the induction currently at HalfQBinomial.lean:177 verbatim, with its `htop`/`hbottom` `have`s replaced by `choose_succ_two (n + 1)` and `choose_succ_two n`. Then inline the successor identity out of `choose_add_succ_two` (DyadicClosedForm.lean:45-48) and `two_mul_choose_succ_two` (:58-61) by calling `choose_succ_two`, and out of DyadicClosedForm.lean:584.

Delete and redirect these actual sites (line numbers corrected):
  - ThueMorseApproximation.lean:206  `choose_succ_two_corrected`
  - ThueMorseGenerating.lean:203     `choose_succ_two_grid`   (NOT 135)
  - ...

**Verifier.** Core content confirmed. All six named declarations exist with exactly the quoted signatures (ThueMorseApproximation.lean:206, ThueMorseGenerating.lean:203, HalfQBinomial.lean:159 and :177, FabiusQBinomialFormula.lean:360, FabiusQBinomialTaylor.lean:145). The decisive pair is real: square_eq_choose_sum (HalfQBinomial.lean:177) and ...

#### `self_le_two_pow` / `succ_le_two_pow` (and `index_le_two_pow` in `Monotonicity`) re-prove Mathlib's `Nat.lt_two_pow_self`, which this repository already uses elsewhere

Confidence high.  `ThueMorsePrefix.lean:324`, `ThueMorsePrefix.lean:332`, `Monotonicity.lean:129`, `NegativeLaplace.lean:143`

**Why.** Three private copies of one Mathlib one-liner, two of them in the same file with textually identical proof scripts. The repository already knows the Mathlib name — `NegativeLaplace.lean:143` writes `Nat.succ_le_of_lt Nat.lt_two_pow_self` and `NegativeLaplaceScaledTailFlat.lean:191` does the same — so this is a case where the author of these two modules evidently did not know the lemma was available.

**Proposal.** Delete the three private duplicates and use the Lean 4 core lemma `Nat.lt_two_pow_self {n : ℕ} : n < 2 ^ n` (Init/Data/Nat/Lemmas.lean:1231 in toolchain v4.32.0; it is `protected`, so keep it fully qualified). Corrected locations: remove `self_le_two_pow` at ThueMorsePrefix.lean:393 and `succ_le_two_pow` at ThueMorsePrefix.lean:401, and `index_le_two_pow` at Monotonicity.lean:129. Corrected use sites: ThueMorsePrefix.lean:423, :437 and :468 (`have hrPow : r ≤ 2 ^ r := self_le_two_pow r` becomes `:= Nat.lt_two_pow_self.le`), ThueMorsePrefix.lean:471 (the two-line `have := succ_le_two_pow r; omega` establishing `hrPowStrict : r < 2 ^ r` collapses to `have hrPowStrict : r < 2 ^ r := Nat.lt_two_pow_self`), and Monotonicity.lean:145 (`exact_mod_cast index_le_two_pow N` becomes `exact_mod_cast Nat.lt_two_pow_self.le`, or `exact_mod_cast (Nat.lt_two_pow_self (n := N)).le` if the implicit argument needs pinning). Note the lemma is Lean core, not Mathlib, so there is no import cost anywhere; the repository already uses it at NegativeLaplace.lean:143 and NegativeLaplaceScaledTailFlat.lean:191.

**Verifier.** The finding survives every adversarial check. (1) All three declarations exist with exactly the quoted signatures and byte-identical proof scripts. (2) The replacement lemma is real: `Nat.lt_two_pow_self : n < 2 ^ n` with auto-bound implicit `n`, at Init/Data/Nat/Lemmas.lean:1231 of toolchain v4.32.0, used by Mathlib at ...

#### The `m = 1` translation-invariance layer of `FabiusQBinomialFormula` is a verbatim copy of the arbitrary-numerator layer, and the bridging lemma `qBinomialThueMorseDyadicFormula 1 n = qBinomialThueMorseFormula n` is never stated

Confidence medium.  `FabiusQBinomialFormula.lean:449`, `FabiusQBinomialFormula.lean:460`, `FabiusQBinomialFormula.lean:474`, `FabiusQBinomialFormula.lean:1051`, `FabiusQBinomialFormula.lean:1072`

**Why.** The two `..._eq_centered`/`..._eq` proofs are token-for-token identical (I diffed them after substituting `thueMorseShiftedPowerSeries k ↦ dyadicNumeratorShiftedPowerSeries m k` and `thueMorseCenteredPowerSum k (n+k) ↦ thueMorseDyadicNumeratorPowerSum m k (n+k)`): the same `Finset.sum_comm` / `Finset.sum_eq_single 0` skeleton, the same `hdle`/`hnpos`/`hdlt`, the same inner `calc`. Their two private feeders duplicate likewise. Since `fabiusAtInverseTwoPow n` is *by definition* `fabiusDyadic n 1` ...

**Proposal.** Re-label as `shorten-proof` plus `new-corollary`, not `deduplicate`: `qBinomialThueMorseTranslatedNumerator_eq_centered` is public API (consumed by FabiusQBinomialTaylor.lean:79,103,198,366 and FabiusRawQBinomialFormula.lean:143) and must keep its statement and its `thueMorseTranslatedPowerSum` vocabulary; only its ~70-line proof is redundant.

In FabiusQBinomialFormula.lean, add two bridge lemmas — each needs a `Fin`-to-`range` conversion in addition to `Nat.one_mul`/`Nat.cast_one`, since `thueMorseCenteredPowerSum`/`thueMorseTranslatedPowerSum` (ThueMorseExponential.lean:44, :225) sum over `Fin (2^k)` while the dyadic sums use `Finset.range (m * 2^k)`:
  `@[simp] theorem thueMorseDyadicNumeratorPowerSum_one (k d : ℕ) : thueMorseDyadicNumeratorPowerSum 1 k d = thueMorseCenteredPowerSum k d` — proof: `rw [thueMorseCenteredPowerSum_eq_sum_range, thueMorseDyadicNumeratorPowerSum]; simp`
  `@[simp] theorem thueMorseDyadicNumeratorTranslatedPowerSum_one (c : ℚ) (k d : ℕ) : thueMorseDyadicNumeratorTranslatedPowerSum c 1 k d = thueMorseTranslatedPowerSum c k d` — proof: `rw ...

**Verifier.** Every cited declaration exists with the quoted signature (`qBinomialThueMorseTranslatedNumerator_eq_centered` at FabiusQBinomialFormula.lean:474, `qBinomialThueMorseDyadicTranslatedNumerator_eq` at :1139, helpers at :449/:460, `thueMorseDyadicNumeratorPowerSum` at :617, `fabiusAtInverseTwoPow := fabiusDyadic n 1` at Arithmetic.lean:377-378). All ...

## Private declarations worth exposing

### Cluster: core

#### `extendedFabius_add_one_eq_rvachevUp` is private, and three downstream modules re-derive it by hand

Confidence high.  `GlobalExtension.lean:294`, `Paper06487Supplement.lean:312`, `NowhereAnalytic.lean:122`, `FabiusTranslatedLegendreSeries.lean:39`

**Why.** This is the identity that makes the whole signed-extension picture concrete — the extension is literally the translate of `up` on the first block — and it is the entry point for three separate downstream arguments (the equation-(32) Rvachev bridge, the nowhere-analyticity transfer, and the translated Legendre series). Each of them currently writes `have hsingle := extendedFabius_eq_single_translate F hF 0 (by simpa using …) (by simpa using …)` followed by `simpa [binaryWeight] using hsingle`, ...

**Proposal.** Keep the proposal as written (drop `private` from `extendedFabius_add_one_eq_rvachevUp` and add the shifted corollary `extendedFabius_eq_rvachevUp_sub_one (F) (hF) {y : ℝ} (hy : y ≤ 2) : extendedFabius F y = rvachevUp F (y - 1)` in GlobalExtension.lean), but correct the call-site list: there are six hand re-derivations of the b = 0 case, not three. In addition to Paper06487Supplement.lean:312-315, NowhereAnalytic.lean:122-126 and FabiusTranslatedLegendreSeries.lean:39-42, the same `extendedFabius_eq_single_translate F hF 0` + `simpa [binaryWeight]` pattern appears at Paper06487Supplement.lean:400-404, FabiusBinaryReductionSeries.lean:253-257, and FabiusBinaryReductionSeries.lean:279-283 (and GlobalDyadic.lean:44-46 instantiates b = 0 at `x = 1 + y` for `extendedFabius_one_add`). All of these have `x <= 2` available in context and can be replaced by a single application of the new corollary. If the `simpa` for the corollary does not fire on `y - 1 + 1`, use `have h : y - 1 + 1 = y := by ring` and `rw [h] at`.

**Verifier.** The finding survives every check. (1) `GlobalExtension.lean:294-306` contains `private lemma extendedFabius_add_one_eq_rvachevUp (F : BoundedFabius) (hF : IsFabius F) {x : ℝ} (hx : x ≤ 1) : extendedFabius F (x + 1) = rvachevUp F x` — quoted verbatim, no misquote. (2) The proposed shifted corollary is true, boundary included: for n >= 1 the summand ...

### Cluster: fourier-legendre

#### hasSum_even_of_odd_eq_zero is private, is duplicated inline in AnalyticMoments, and is a two-line consequence of Function.Injective.hasSum_iff

Confidence medium.  `FabiusLegendreSeries.lean:80`, `AnalyticMoments.lean:1116`

**Why.** Two things at once. First, the statement has no Fabius content whatsoever and is genuinely reusable, so `private` is the wrong visibility. Second, `rvachevFourier_eq_momentSeries` (AnalyticMoments.lean:1101ff) reimplements it inline with the identical chain `comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))` → `hasSum_zero` → `HasSum.even_add_odd` → `HasSum.unique` → rewrite; the proof is duplicated because the named version is hidden behind `private` in a downstream module. Third, ...

**Proposal.** Move the lemma out of FabiusLegendreSeries.lean:80 into MomentPowerSeries.lean (verified upstream of both AnalyticMoments and FabiusLegendreSeries), drop `private`, and use the minimal typeclasses that Function.Injective.hasSum_iff actually requires:

/-- If every odd term of a series vanishes, the sum is already the sum of the even
subsequence. -/
theorem hasSum_even_of_odd_eq_zero {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    {f : ℕ → E} {a : E}
    (h : HasSum f a) (hodd : ∀ n, f (2 * n + 1) = 0) :
    HasSum (fun n ↦ f (2 * n)) a :=
  ((mul_right_injective₀ (two_ne_zero' ℕ)).hasSum_iff (fun x hx => by
      rcases Nat.even_or_odd x with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exact absurd ⟨k, by omega⟩ hx
      · exact hodd k)).mpr h

Corrections to the original proposal:
- `Function.Injective.hasSum_iff` is the `@[to_additive]` image of `Function.Injective.hasProd_iff` at Mathlib v4.32.0 `Mathlib/Topology/Algebra/InfiniteSum/Defs.lean:231`, NOT `.../InfiniteSum/Basic.lean`.
- It lives under `variable [CommMonoid α] [TopologicalSpace α]` (Defs.lean:72), with `[T2Space α] [L.NeBot]` ...

**Verifier.** All five checks pass on substance. (1) FabiusLegendreSeries.lean:80 holds `private theorem hasSum_even_of_odd_eq_zero` with exactly the quoted signature and body; AnalyticMoments.lean:1116-1133 reimplements it verbatim (comp_injective (mul_right_injective₀ (two_ne_zero' ℕ)) -> hasSum_zero -> HasSum.even_add_odd -> .unique -> rw), same type role ...

### Cluster: lambert-asymptotics

#### `abs_log_sub_log_le_div`, a general logarithm Lipschitz bound with no Fabius content, is buried as `private`

Confidence medium.  `FabiusLambertAllOrderRemainder.lean:589`, `FabiusLambertAllOrderRemainder.lean:629`

**Why.** This is a standalone, quantitative, fully general statement — the mean-value Lipschitz bound for `Real.log` on a right ray — with no reference to any Fabius, Lambert, or saddle notion. It is exactly the tool needed to run a contraction/stability argument for any fixed-point equation of the form `u - log u / c = t`, which is how it is used here (FabiusLambertAllOrderRemainder.lean:629, inside `truncatedPhase_sub_dyadicLambertPhase_abs_le`). Marking it `private` means the next stability argument ...

**Proposal.** Drop `private` and add a doc comment, but move the declaration to LowerLambertW.lean rather than leaving it at FabiusLambertAllOrderRemainder.lean:589. Rationale for the move: FabiusLambertAllOrderRemainder.lean is a near-leaf module (only FabiusLambertAllOrderSmallArgument.lean imports it) with 38 private declarations against 1 public theorem, and its transitive closure is the whole Lambert/saddle/power-series stack — so exposing a general two-line log fact there still forces any future consumer to import that entire stack, defeating the stated reuse benefit. LowerLambertW.lean is the correct low-import host: it is already in `namespace Fabius`, imports only Mathlib (Mathlib.Analysis.SpecialFunctions.Log.Monotone, Pow.Real, Topology.Order.IntermediateValue — Log.Monotone transitively supplies Real.log_div, Real.log_le_log, and Real.log_le_sub_one_of_pos, so no new import is needed), and is already inside FabiusLambertAllOrderRemainder's import closure via FabiusLambertSaddle -> FabiusLambertPhase -> LowerLambertW, so the existing call site at line 629 keeps resolving unchanged with ...

**Verifier.** All five checks pass. (1) The declaration exists verbatim at FabiusLambertAllOrderRemainder.lean:589-591 with exactly the quoted signature, inside `namespace Fabius` (lines 22-702), and is used exactly as claimed at line 629 inside `truncatedPhase_sub_dyadicLambertPhase_abs_le` (line 620). (2) The statement is true (MVT on [K,infinity): |log a - ...

### Cluster: moments-probability

#### The three private `unitLaplaceMoment_*` estimates are proved only for `weightedSumDistribution` but their proofs are generic in any finite measure

Confidence high.  `LaplaceMomentBounds.lean:28`, `LaplaceMomentBounds.lean:86`, `LaplaceMomentBounds.lean:118`, `LaplaceMomentBounds.lean:141`, `EndpointLaplaceComparison.lean:233`

**Why.** `pow_mul_exp_neg_quarter_le` mentions neither Fabius nor any measure — it is the elementary `x^k e^{-y} ≤ k!` scaling bound and has independent interest. The two Laplace estimates are the standard log-convexity and factorial-moment bounds for the Laplace transform of any measure on `[0,1]`; hiding them behind one particular distribution makes them unusable for the other measures in the corpus (`polynomialMeasure`, `finiteConvolutionMeasure`, `rvachevMeasure`), all of which are probability ...

**Proposal.** Move FOUR declarations (not three) from LaplaceMomentBounds.lean into EndpointLaplaceComparison.lean, immediately after unitLaplaceMoment_nonneg (line 236), as public and measure-generic, using the module's existing [IsFiniteMeasureOnCompacts μ] convention rather than [IsFiniteMeasure μ]:

/-- `x ^ k * exp (-(s * x / 4)) ≤ (4 / s) ^ k * k!` for `0 ≤ x`, `0 < s`.  No measure involved. -/
theorem pow_mul_exp_neg_quarter_le (k : ℕ) {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    x ^ k * Real.exp (-(s * x / 4)) ≤ (4 / s) ^ k * (k.factorial : ℝ)

/-- Cauchy–Schwarz form of Hölder log-convexity for the tilted mass on `[0,1]`. -/
theorem unitLaplaceMoment_three_quarters_le_sqrt (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (s : ℝ) (hs : 0 ≤ s) :
    unitLaplaceMoment μ (3 * s / 4) 0 ≤
      unitLaplaceMoment μ (s / 2) 0 ^ (1 / 2 : ℝ) * unitLaplaceMoment μ s 0 ^ (1 / 2 : ℝ)

/-- Squared form of the same log-convexity bound. -/
theorem unitLaplaceMoment_three_quarters_sq_le (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (s : ℝ) (hs : 0 ≤ s) :
    unitLaplaceMoment μ (3 * s / 4) 0 ^ 2 ≤
     ...

**Verifier.** The core finding holds and I could positively confirm it. All four cited private lemmas exist at LaplaceMomentBounds.lean:28/86/118/141 with exactly the quoted signatures, and unitLaplaceMoment/unitLaplaceMoment_nonneg are generic in (μ : Measure ℝ) at EndpointLaplaceComparison.lean:233/236 as claimed. Reading the proof bodies confirms the only ...

### Cluster: negative-laplace

#### `negativeLaplaceKernel_eq_log_sub_log` is `private` and is therefore re-proved verbatim downstream as `boseLogKernel_eq_negativeLaplaceKernel_add_log`; `exp_negativeLaplaceKernel` and `exp_neg_lt_one` are in the same position

Confidence high.  `NegativeLaplace.lean:288`, `NegativeLaplace.lean:377`, `NegativeLaplace.lean:118`, `BoseFinitePartIntegral.lean:436`, `NegativeLaplaceVertical.lean:33`

**Why.** `boseLogKernel_eq_negativeLaplaceKernel_add_log` is the same equation as `negativeLaplaceKernel_eq_log_sub_log` rearranged, re-derived from `Real.log_div` with a hand-rolled side condition, in a module that (verified by import closure) already sees `NegativeLaplace`. `0 < 1 - Real.exp (-x)` is re-derived from scratch at least twenty times across this cluster (NegativeLaplace.lean:118, NegativeLaplaceDerivativeBounds.lean:40, NegativeLaplaceMinorArc.lean:35 and :59, ...

**Proposal.** In `NegativeLaplace.lean`, expose and document the two logarithm lemmas by deleting `private` (no other change needed):

/-- The logarithmic Laplace factor split into its two logarithms. -/
theorem negativeLaplaceKernel_eq_log_sub_log (s : ℝ) (hs : 0 < s) :
    negativeLaplaceKernel s = Real.log (1 - Real.exp (-s)) - Real.log s   -- line 288

/-- Exponentiating the logarithmic factor recovers the Laplace factor. -/
theorem exp_negativeLaplaceKernel (x : ℝ) (hx : 0 < x) :
    Real.exp (negativeLaplaceKernel x) = (1 - Real.exp (-x)) / x          -- line 377

For the positivity fact, do NOT describe this as un-privatizing: the existing lemma is `private lemma exp_neg_lt_one (x : ℝ) (hx : 0 < x) : Real.exp (-x) < 1` (line 118), a different statement. Either (a) simply drop its `private` and let callers keep writing `sub_pos.mpr (exp_neg_lt_one _ h)`, or (b) add next to it the public form

/-- The positive-argument denominator of the Laplace factor never vanishes. -/
theorem one_sub_exp_neg_pos {x : ℝ} (hx : 0 < x) : 0 < 1 - Real.exp (-x) :=
  sub_pos.mpr (exp_neg_lt_one x hx)

leaving ...

**Verifier.** All five refutation checks fail to break the finding.

(1) Signatures verified verbatim. `NegativeLaplace.lean:288` is `private lemma negativeLaplaceKernel_eq_log_sub_log (s : ℝ) (hs : 0 < s) : negativeLaplaceKernel s = Real.log (1 - Real.exp (-s)) - Real.log s`; `:377` is `private lemma exp_negativeLaplaceKernel (x : ℝ) (hx : 0 < x) : Real.exp ...

### Cluster: papers-aggregates

#### `iteratedDeriv_extendedFabius_zero` sits downstream of the module that needs it, forcing an inline re-proof in `TaylorReduction`

Confidence medium.  `Paper06487Supplement.lean:165`, `TaylorReduction.lean:153`, `GlobalExtension.lean:273`

**Why.** The project invariant says a declaration belongs in the upstream-most module that can state it. Both ingredients of this proof — `iteratedDeriv_extendedFabius` (GlobalExtension.lean:273) and `extendedFabius_eq_zero_of_nonpos` — live in `GlobalExtension.lean`, so the lemma could have been stated there. Because it was instead placed in `Paper06487Supplement` (which imports `PaperStatements`, which imports `TaylorReduction`), the upstream `TaylorReduction.lean` cannot reach it and re-derives it by ...

**Proposal.** Move `iteratedDeriv_extendedFabius_zero` from Paper06487Supplement.lean:165-171 into GlobalExtension.lean, inserting it after the END of `iteratedDeriv_extendedFabius` — that proof runs to line 292 and the next declaration (`private lemma extendedFabius_add_one_eq_rvachevUp`) begins at line 294, so the insertion point is line 293, not line 273 as the proposal states. Keep the name, namespace (`Fabius`), signature, doc comment, and the existing proof body unchanged:

/-- Every derivative of the signed global Fabius function vanishes at zero. -/
theorem iteratedDeriv_extendedFabius_zero
    (F : BoundedFabius) (hF : IsFabius F) (order : ℕ) :
    iteratedDeriv order (extendedFabius F) 0 = 0 := by
  rw [iteratedDeriv_extendedFabius F hF, mul_zero,
    extendedFabius_eq_zero_of_nonpos F hF (by norm_num)]
  ring

Then replace TaylorReduction.lean:153-159 with:
    have hzeroDeriv : ∀ k : ℕ, iteratedDeriv k (extendedFabius F) 0 = 0 :=
      fun k => iteratedDeriv_extendedFabius_zero F hF k

Caveat to observe when executing: although GlobalExtension is not one of the three modules ...

**Verifier.** Every element of the finding checks out against the source. (1) Signatures: Paper06487Supplement.lean:165-171 contains `iteratedDeriv_extendedFabius_zero (F : BoundedFabius) (hF : IsFabius F) (order : ℕ) : iteratedDeriv order (extendedFabius F) 0 = 0` with the exact three-line proof quoted; TaylorReduction.lean:153-159 contains the `hzeroDeriv` ...

### Cluster: saddle

#### `norm_standardGaussian` lives downstream of `standardGaussian` and is therefore re-proved inline four times, once in a module that already imports it

Confidence high.  `GaussianPolynomialContraction.lean:53`, `QuantitativeSaddle.lean:27`, `FabiusSaddleCentral.lean:173`, `SaddleAllOrders.lean:64`, `FabiusSaddleReferenceTail.lean:109`

**Why.** `standardGaussian` is defined in `QuantitativeSaddle.lean:27`; the one-line fact about its norm is currently stated in `GaussianPolynomialContraction.lean`, which is *not* in the import closure of `FabiusSaddleCentral` (48 modules) or `SaddleAllOrders` (2 modules). Those two modules therefore have to re-prove it, and `FabiusSaddleReferenceTail` and `FabiusSaddleMassAllOrders` re-prove it too even though `FabiusSaddleMassAllOrders` does import `GaussianPolynomialContraction` — i.e. its author ...

**Proposal.** Move the norm lemma next to the definition it is about. In `QuantitativeSaddle.lean`, immediately after `standardGaussian` (line 28-29) and before `integrable_standardGaussian` (line 31), add — WITHOUT `@[simp]`:

/-- The norm of the complex-valued standard Gaussian is the real Gaussian
kernel. -/
theorem norm_standardGaussian (v : ℝ) :
    ‖standardGaussian v‖ = Real.exp (-(v ^ 2) / 2) := by
  rw [standardGaussian, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

The `@[simp]` in the original proposal must be dropped: the existing declaration carries no simp attribute, and adding one changes the simp normal form for the 52 modules downstream of QuantitativeSaddle with no compile evidence that nothing breaks.

Then replace the body of `Fabius.SaddleExpansion.norm_standardGaussian` at `GaussianPolynomialContraction.lean:53-57` by the forwarding proof, preserving its name and import path (it is used at GaussianPolynomialContraction.lean:276):

theorem norm_standardGaussian (v : ℝ) :
    ‖QuantitativeSaddle.standardGaussian v‖ =
      Real.exp (-(v ^ 2) / 2) :=
  ...

**Verifier.** The finding survives verification on every substantive point, but its line numbers and its `@[simp]` suggestion need correction.

CONFIRMED:
1. `Fabius.SaddleExpansion.norm_standardGaussian` exists at GaussianPolynomialContraction.lean:53 with exactly the quoted signature and the quoted four-rewrite proof. Not misquoted.
2. `standardGaussian` is ...

#### `expCoeff_one` and `expCoeff_two` are missing from the generic algebra and exist only as a private `Polynomial ℂ`-specific copy

**DONE** by the asymptotic-expansion branch, in
`FabiusSecondSaddleCorrection.lean` and `FabiusSaddleLeadingCoefficient.lean`.
Ten generic declarations over `[CommRing R] [Algebra ℚ R]` close the gap:
`natCast_succ_mul_expCoeff_succ`, `expCoeff_one`, `two_mul_expCoeff_two`,
`six_mul_expCoeff_three`, `twentyFour_mul_expCoeff_four`, `expCoeff_two`,
`expCoeff_three`, `expCoeff_four`,
`twentyFour_mul_expCoeff_four_of_sq_eq_neg_one`, `two_mul_logCoeff_two`.  They
come in denominator-cleared and rational-scaled pairs, because a commutative
`ℚ`-algebra need not be a field.  Two further generic lemmas were added
alongside: `expCoeff_succ_eq_add` and `expCoeff_sub_self_congr`, the second
recording that the exponential recurrence is affine in its top exponent
coefficient, which is what makes the leading-coefficient law provable at
general order rather than checkable order by order.

Landed downstream-most rather than in `SaddleExpansionAlgebra.lean`, with doc
comments naming that module as the correct long-term home.  This is the
opposite call from the triangular-identity entry above, and deliberately so:
pay a root-module invalidation to REMOVE duplication that already exists, never
to pre-position a new declaration that has no duplicates yet.

Confidence high.  `FabiusSaddleExpansionCoefficients.lean:273`, `SaddleExpansionAlgebra.lean:51`, `SaddleLogExpansionAlgebra.lean:44`, `SaddleLogExpansionAlgebra.lean:49`

**Why.** Category-1 and category-3 at once: the private lemma's statement is pinned to `Polynomial ℂ` and to the ℂ-scalar action, but its content is a two-line unfolding of the generic `expCoeff` recurrence that holds in every `[CommRing R] [Algebra ℚ R]`. The sibling module `SaddleLogExpansionAlgebra.lean` already exposes exactly the analogous `logCoeff_one` (`@[simp]`) and `logCoeff_two` generically, so the exponential side is asymmetrically missing its two lowest-order evaluations — the ones every ...

**Proposal.** Add to SaddleExpansionAlgebra.lean immediately after `expCoeff_succ` (line 59), inside the existing `variable {R : Type*} [CommRing R] [Algebra ℚ R]` context:

/-- The first exponential coefficient is the first exponent coefficient. -/
@[simp] theorem expCoeff_one (E : ℕ → R) : expCoeff E 1 = E 1 := by
  rw [show 1 = 0 + 1 by omega, expCoeff_succ]
  simp

/-- The second exponential coefficient. -/
theorem expCoeff_two (E : ℕ → R) :
    expCoeff E 2 = E 2 + ((2 : ℚ)⁻¹) • (E 1 * E 1) := by
  rw [show 2 = 1 + 1 by omega, expCoeff_succ]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.sub_zero, Nat.sub_self, expCoeff_zero, expCoeff_one,
    Nat.cast_zero, Nat.cast_one, zero_add, one_mul, mul_one]
  rw [smul_add, add_comm]
  congr 1
  -- remaining goal: ((2 : ℚ)⁻¹) • ((1 + 1 : R) * E 2) = E 2
  rw [Algebra.smul_def, show ((1 : R) + 1) = algebraMap ℚ R (2 : ℚ) by norm_num,
    ← mul_assoc, ← map_mul, inv_mul_cancel₀ (by norm_num : (2 : ℚ) ≠ 0),
    map_one, one_mul]

`expCoeff_one` is straightforward (`simp` suffices, since `expCoeff_zero` is already `@[simp]`). ...

**Verifier.** The substance survives verification. FabiusSaddleExpansionCoefficients.lean:273 is exactly the private `expCoeff_two (E : ℕ → Polynomial ℂ) : expCoeff E 2 = E 2 + (1/2 : ℂ) • (E 1 * E 1)` as quoted; SaddleExpansionAlgebra.lean:51 is `expCoeff_zero` and the module stops there; a grep of all 176 modules turns up only two occurrences of `expCoeff E ...

#### A general polynomial fact about `divX` iteration is buried as a private helper

Confidence medium.  `SaddleExpansionFiniteRemainder.lean:140`, `FabiusSaddleReferenceWeight.lean:79`, `FabiusSaddleReferenceWeight.lean:86`

**Why.** None of the three mentions the saddle expansion, the Fabius function, or `expCoeff`; they are statements about `Polynomial.divX` that any user of `finiteExpSubstitutionQuotient` will need, since that definition is `Polynomial.divX^[L]` applied to the defect. Two of them are declared in a downstream module even though `SaddleExpansionFiniteRemainder` — where `divX^[L]` is introduced — is the natural and upstream-most home, and `FabiusSaddleReferenceWeight.lean` imports it directly (line 3).

**Proposal.** Collect the three into a public `divX`-iteration section in `SaddleExpansionFiniteRemainder.lean`, and delete the two private copies at `FabiusSaddleReferenceWeight.lean:78` and `:85`. Placement and binders must be explicit — do NOT rely on the file's section `variable`: put the block after `noncomputable section` (line 11) but give each lemma its own binders, because the file sets `autoImplicit false` (line 4) so a bare `R` above line 13 fails to elaborate, while below line 13 Lean's instance-binder inclusion silently adds `[Algebra ℚ R]` to what is supposed to be a general polynomial fact. Concretely, in namespace `Fabius.SaddleExpansion`:

/-- Multiplying back by `X ^ L` undoes `L` applications of `divX` when the first
`L` coefficients vanish. -/
theorem X_pow_mul_iterate_divX_eq_of_coeff_zero
    {S : Type*} [CommRing S] (p : Polynomial S) (L : ℕ)
    (hzero : ∀ k < L, p.coeff k = 0) :
    Polynomial.X ^ L * (Polynomial.divX^[L]) p = p

/-- `divX` commutes with coefficientwise ring maps. -/
theorem map_divX {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (p : ...

**Verifier.** Every factual claim survives adversarial checking. (1) All three declarations exist at the cited spots with the quoted signatures: SaddleExpansionFiniteRemainder.lean:140 `private lemma X_pow_mul_iterate_divX_eq_of_coeff_zero` (used once, at line 163), and FabiusSaddleReferenceWeight.lean:78 `private theorem map_divX` / :85 `private theorem ...

## Proof shortening

### Cluster: dyadic

#### `ExactInversePower` re-proves three positivity lemmas that already exist in `Arithmetic`

Confidence high.  `ExactInversePower.lean:69`, `ExactInversePower.lean:74`, `ExactInversePower.lean:79`, `Arithmetic.lean:103`, `Arithmetic.lean:115`

**Why.** The three inline `have`s are character-for-character the bodies of the three named lemmas in Arithmetic.lean (`unfold X; apply Finset.prod_pos; intro k hk; exact Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) (by omega))`). The author evidently did not know they were already there, even though the same proof uses `mersenneProduct_succ_eq`, `evenMersenneProduct_succ_eq` and `oddMersenneProduct_succ_eq` from the same section of Arithmetic.lean.

**Proposal.** `ExactInversePower` and `PaperStatements` re-prove positivity lemmas that already exist in `Arithmetic`.

In `ExactInversePower.lean`, replace lines 69-83 (fifteen lines) with three:

  have hoddPos : 0 < oddDoubleFactorial (n + 1) := oddDoubleFactorial_pos (n + 1)
  have hevenPos : 0 < evenMersenneProduct n := evenMersenneProduct_pos n
  have hoddMerPos : 0 < oddMersenneProduct n := oddMersenneProduct_pos n

In `PaperStatements.lean`, replace lines 426-435 (ten lines) inside `theorem_seven` with two:

  have hoddPos : 0 < oddDoubleFactorial (n + 1) := oddDoubleFactorial_pos (n + 1)
  have hevenPos : 0 < evenMersenneProduct n := evenMersenneProduct_pos n

using the already-public
  Arithmetic.lean:103  theorem oddDoubleFactorial_pos (n : ℕ) : 0 < oddDoubleFactorial n
  Arithmetic.lean:115  theorem evenMersenneProduct_pos (n : ℕ) : 0 < evenMersenneProduct n
  Arithmetic.lean:122  theorem oddMersenneProduct_pos (n : ℕ) : 0 < oddMersenneProduct n

Corrected rationale: the two Mersenne blocks are character-for-character the bodies of `evenMersenneProduct_pos`/`oddMersenneProduct_pos` ...

**Verifier.** The finding holds. All six cited locations are accurate and the quoted signatures are exact. Arithmetic.lean:103/115/122 declare `oddDoubleFactorial_pos`, `evenMersenneProduct_pos`, `oddMersenneProduct_pos` as plain public theorems in `namespace Fabius`, each universally quantified over `n : ℕ` with no hypotheses, so the substitution has no ...

### Cluster: lambert-asymptotics

#### `real_log_second_order_isBigO` is a six-line consequence of a Mathlib lemma the corpus already uses elsewhere

Confidence medium.  `FabiusLogMainDefect.lean:23`, `FabiusLambertAllOrderRemainder.lean:401`

**Why.** Mathlib has `Real.abs_log_sub_add_sum_range_le {x : ℝ} (h : |x| < 1) (n : ℕ) : |(∑ i ∈ range n, x ^ (i + 1) / (i + 1)) + log (1 - x)| ≤ |x| ^ (n + 1) / (1 - |x|)` (Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean:217, confirmed present in the pinned Mathlib). Substituting `x := -x` and `n := 2` gives `|(-x + x²/2) + log (1 + x)| ≤ |x|³ / (1 - |x|)`, which is the target up to `ring` and `(1 - |x|)⁻¹ ≤ 2`. The author of FabiusLogMainDefect.lean instead routed through ...

**Proposal.** /-- Second-order Taylor bound for `log (1 + x)` near zero. -/
lemma real_log_second_order_isBigO :
    (fun x : ℝ => Real.log (1 + x) - x + x ^ 2 / 2) =O[𝓝 0]
      (fun x : ℝ => x ^ 3) := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0:ℝ) < 1/2)] with x hx
  have hx' : |x| < 1 / 2 := by simpa [Real.dist_0_eq_abs] using hx
  have h0 := Real.abs_log_sub_add_sum_range_le (x := -x)
    (by simpa using hx'.trans (by norm_num : (1 : ℝ) / 2 < 1)) 2
  -- h0 : |(∑ i ∈ range 2, (-x) ^ (i+1) / (i+1)) + Real.log (1 - -x)|
  --        ≤ |-x| ^ (2+1) / (1 - |-x|)
  rw [show (1 : ℝ) - -x = 1 + x by ring, abs_neg] at h0
  norm_num at h0
  have h : |Real.log (1 + x) - x + x ^ 2 / 2| ≤ |x| ^ 3 / (1 - |x|) := by
    refine le_trans (le_of_eq (congrArg abs ?_)) h0
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith [abs_nonneg x])]
  nlinarith [pow_nonneg (abs_nonneg x) 3]

-- Additionally: replace line 2 ...

**Verifier.** The finding survives verification on substance, with two corrections to its details.

CONFIRMED: (1) `real_log_second_order_isBigO` is at FabiusLogMainDefect.lean:23 with the quoted signature, and its proof (lines 26-56) is 31 lines routed through `Complex.norm_log_sub_logTaylor_le 2`, an ofReal cast, and a `(1-|x|)⁻¹ ≤ 2` step. (2) ...

### Cluster: moments-probability

#### Two proofs re-derive an adjacent lemma verbatim instead of applying it

Confidence high.  `AnalyticMoments.lean:610`, `AnalyticMoments.lean:640`, `LaplaceMoments.lean:246`, `LaplaceMoments.lean:189`, `LaplaceMoments.lean:265`

**Why.** In (a) the duplicated block sits two lines above the lemma it duplicates, so the reader has no way to know they are the same computation; in (b) the second induction differs from the first only by the missing `hindex : k + n + 1 = k + (n + 1)` step, i.e. it is literally the `k = 0` instance re-run. Both are pure maintenance liabilities: an edit to the reusable lemma leaves the copy behind.

**Proposal.** (a) Unchanged and confirmed: move `private lemma shifted_laplace_plus` (AnalyticMoments.lean:640-670) to sit anywhere after line 548 (it needs only `rvachevLaplace`, defined at line 523, plus `intervalIntegral.smul_integral_comp_mul_sub`), delete lines 610-637 of `complexGeneratingFunction_eq_exp_mul_laplace`, and end that proof with `rw [hgen, shifted_laplace_plus F z]`. 28 lines removed, no signature change.

(b) Same idea, corrected line count (~10 lines, not ~14) and a defeq-based spelling that does not depend on simp accepting a lambda-headed rewrite rule. Replace the body of `iteratedDeriv_generatingFunction_neg` (LaplaceMoments.lean:250-261) with

  simpa using iteratedDeriv_fabiusLaplaceMoment F hF 0 n s

(`fabiusLaplaceMoment F 0` is defeq to `fun x => generatingFunction F (-x)` because `fabiusLaplaceMoment_zero` is `rfl`, so the closing `exact` unifies at default transparency; simp only has to turn `0 + n` into `n`). If that unification is rejected, fall back to the finding's explicit form:

  have hfun : (fun x => generatingFunction F (-x)) = fabiusLaplaceMoment F 0 :=
   ...

**Verifier.** Both halves survive adversarial checking. (a) A byte-level diff of AnalyticMoments.lean:610-628 against 645-663 is IDENTICAL (same `let g`, `hsub0`, `hcongr`, `hsub`); lines 629-637 and 664-670 run the same rewrite chain, differing only by packaging as `have hfactor`. `shifted_laplace_plus` exists at line 640 with exactly the quoted statement, ...

### Cluster: papers-aggregates

#### `PaperStatements.lean` re-proves `oddDoubleFactorial_pos` and `evenMersenneProduct_pos` inline three times instead of using the public Arithmetic lemmas

Confidence high.  `PaperStatements.lean:426`, `PaperStatements.lean:431`, `PaperStatements.lean:483`, `PaperStatements.lean:567`, `PaperStatements.lean:572`

**Why.** `Fabius.oddDoubleFactorial_pos (n : ℕ) : 0 < oddDoubleFactorial n` (Arithmetic.lean:103) and `Fabius.evenMersenneProduct_pos (n : ℕ) : 0 < evenMersenneProduct n` (Arithmetic.lean:115) are public and have exactly these proofs (`unfold; Finset.prod_pos ...` and `unfold; Finset.prod_pos; Nat.sub_pos_of_lt (Nat.one_lt_pow ...)`). They are already used correctly elsewhere (DenominatorBound.lean:176-177, NormalizedEvenMoments.lean:67), so the author knew of them for other files but re-derived them by ...

**Proposal.** Replace the hand-rolled positivity blocks with the existing public Arithmetic lemmas at all four sites (no new declarations, no signature changes):

PaperStatements.lean:426-435 (theorem_seven):
  have hoddPos : 0 < oddDoubleFactorial (n + 1) := oddDoubleFactorial_pos _
  have hevenPos : 0 < evenMersenneProduct n := evenMersenneProduct_pos _

PaperStatements.lean:483-492 (reshetnikov_even_eq_sum):
  have hdenPos : 0 < oddDoubleFactorial (k + 1) * evenMersenneProduct k :=
    Nat.mul_pos (oddDoubleFactorial_pos _) (evenMersenneProduct_pos _)

PaperStatements.lean:567-576 (theorem_nine; note the actual indices are `2 * m` and `m`, not `n + 1` and `n`):
  have hoddPos : 0 < oddDoubleFactorial (2 * m) := oddDoubleFactorial_pos _
  have hevenPos : 0 < evenMersenneProduct m := evenMersenneProduct_pos _

Additional site the original finding omitted — ExactInversePower.lean:69-83, which repeats the same pattern three times and can use the third public lemma `oddMersenneProduct_pos` (Arithmetic.lean:122):
  have hoddPos : 0 < oddDoubleFactorial (n + 1) := oddDoubleFactorial_pos _
  have ...

**Verifier.** Confirmed on every point. (1) Both named replacement lemmas exist with exactly the stated signatures and are public in `namespace Fabius`: `oddDoubleFactorial_pos (n : ℕ) : 0 < oddDoubleFactorial n` at Arithmetic.lean:103 and `evenMersenneProduct_pos (n : ℕ) : 0 < evenMersenneProduct n` at Arithmetic.lean:115 (namespace opened at ...

### Cluster: regularity

#### Three private helper lemmas already exist in Mathlib (and two of them duplicate each other)

Confidence high.  `GlobalBounds.lean:105`, `BoundedDerivatives.lean:58`, `Monotonicity.lean:129`

**Why.** `iteratedDeriv_zero_fun` and `iteratedDeriv_const_succ` are the same statement written twice in two modules of this cluster (one specialised to `c = 0`, the other to positive order), and both are instances of a single Mathlib lemma. `index_le_two_pow` is a six-line induction for a Mathlib one-liner. Removing them removes ~20 lines and two hand-rolled inductions from the regularity cluster.

**Proposal.** Title: Three private helper lemmas are each subsumed by an existing Mathlib/core lemma (they are NOT duplicates of one another).

Delete all three private declarations and replace the call sites:

* GlobalBounds.lean:105-112 — delete `iteratedDeriv_zero_fun`. Call site GlobalBounds.lean:130 becomes:
  `rw [hEq.iteratedDeriv_eq n]; exact iteratedDeriv_fun_const_zero`
  (`iteratedDeriv_fun_const_zero`, `@[simp]`, Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean:370; `simp` also closes it.)

* BoundedDerivatives.lean:58-68 — delete `iteratedDeriv_const_succ`. Call site BoundedDerivatives.lean:78 becomes:
  `rw [heq.iteratedDeriv_eq (m + 1)]; simp [iteratedDeriv_const]`
  (`iteratedDeriv_const`, Defs.lean:357. Prefer this over `rw [..., iteratedDeriv_const, if_neg (Nat.succ_ne_zero m)]`, which additionally relies on `m + 1` unifying with `Nat.succ m` inside the rewrite.)

* Monotonicity.lean:129-135 — delete `index_le_two_pow`. Call site Monotonicity.lean:144-145 becomes:
  `have hNle : (N : ℝ) ≤ (2 : ℝ) ^ N := by exact_mod_cast (Nat.lt_two_pow_self (n := N)).le`
  ...

**Verifier.** The actionable core survives verification against the pinned versions (Lean core v4.32.0, Mathlib rev 81a5d257c8e410db227a6665ed08f64fea08e997 / v4.32.0). All three private declarations exist at the cited lines with the quoted signatures (GlobalBounds.lean:105, BoundedDerivatives.lean:58, Monotonicity.lean:129), each with exactly one call site ...

## Documentation

### Cluster: discrete-limits-computability

#### About sixty public declarations in this cluster carry no doc comment, violating the project invariant

Confidence high.  `FabiusComputableSpline.lean:27`, `FabiusComputableSpline.lean:105`, `FabiusComputableSpline.lean:148`, `FabiusComputableSpline.lean:159`, `FabiusComputableSpline.lean:199`

**Why.** The project states as an invariant that every non-private declaration carries a doc comment. In FabiusComputableSpline.lean the gap covers the whole primitive-recursive layer — `tmBitPR`, `splineTermPR`, `splineSumsPR`, `splineDenPR`, `splineCodePR`, `rawSplineNumerator`, `rawSplineValue`, `SignedRatCode`, `fabiusSplineApproxPR_error` — which is precisely the part a reader cannot reconstruct from the names, since these are algorithmic encodings whose relation to the mathematics is the content ...

**Proposal.** Fifty-nine (not fifty-eight) non-`private` declarations in this cluster carry no `/-- ... -/` doc comment, at HEAD affa557d28b2c1eb51348f5eed300cf8f35b1f13: 28 in FabiusComputableSpline.lean, 24 in FabiusUniformSpline.lean, 5 in FabiusDiscreteLimitToeplitz.lean, 1 in FabiusComputability.lean, 1 in FabiusDiscreteLimitComplexShift.lean; FabiusDiscreteLimitIntegration.lean, FabiusComplexMGF.lean, FabiusComplexShiftSpline.lean, FabiusParityPowerSeries.lean and BernoulliRecurrences.lean are clean. Address the declarations by NAME, not by line: the cited line numbers are already stale (FabiusUniformSpline.lean shifted about 41 lines when the Thue-Morse block lemmas were de-triplicated, moving the five cited theorems to 985/1001/1011/1189/1266).

The FabiusComputableSpline.lean list is: tmBitPR, tmBitPR_zero (the one the original scan missed, an `@[simp] theorem` on a single line), tmBitPR_of_pos, tmBitPR_eq_thueMorseBit, tmBitPR_primrec, splineTermPR, splineSumsPR, splineSumsPR_primrec, splineDenPR, splineDenPR_primrec, splineDenPR_eq, SignedRatCode, splineCodePR, splineCodePR_primrec, ...

**Verifier.** The finding survives verification, with corrections. All 22 cited file:line locations resolve to real declarations that genuinely carry no preceding `/-- ... -/` doc comment and are not `private`, and no `@[inherit_doc]` covers them. All five quoted signatures are verbatim (only line-wrapping differs on `fabiusSplineApproxPR_error`). The invariant ...

### Cluster: dyadic

#### Fifty-nine public declarations in the cluster have no doc comment, including cross-module API

Confidence high.  `DyadicClosedForm.lean:23`, `DyadicClosedForm.lean:53`, `DyadicClosedForm.lean:66`, `DyadicClosedForm.lean:86`, `DyadicClosedForm.lean:234`

**Why.** The project invariant is a doc comment on every non-private declaration, and DyadicClosedForm.lean — the largest module in the cluster at 1143 lines — has zero doc comments on 40 of its public declarations while its module header describes the file as a whole. These are not internal helpers: `two_mul_choose_succ_two` is cited from FabiusDiscreteLimitIntegration.lean:29/36, FabiusParityPowerSeries.lean:33, FabiusQBinomialTaylor.lean:150/220/221 and HalfQBinomial.lean:155; `choose_add_succ_two` ...

**Proposal.** Add a doc comment to each of the 63 (not 59) undocumented non-private top-level declarations in the four modules, at these HEAD (commit 25fa3e9d1) line numbers. Do NOT use the line numbers in the original finding: they were taken against commit 3e35001c3 and the last nine DyadicClosedForm entries are off by +22; entry :1077 in particular points into the statement of `fabiusDyadic_add_remainder_eq_block`, which is already documented at 1074-1076, and :958 / :1132 point into proof bodies (`induction b with`, `let b := Nat.log2 a`), so a literal edit there breaks the build.

DyadicClosedForm.lean — 44 declarations: 23 choose_mul_choose_disjoint, 36 choose_add_succ_two, 53 two_mul_choose_succ_two, 66 sum_fin_add, 73 sum_fin_two_mul, 86 binaryWeight_add_pow_two, 101 binaryWeight_two_mul, 110 binaryWeight_two_mul_add_one, 118 thueMorseSign_two_mul, 122 thueMorseSign_two_mul_add_one, 126 thueMorse_sum_two_mul, 145 thuePowerSum_succ, 194 thuePowerSum_eq_zero_of_lt, 207 thueMorse_affine_power_sum_eq_zero, 229 thueMorseSign_add_pow_two, 234 thueMorse_sum_split, 259 dyadicKernel_eq_sum_range, ...

**Verifier.** The substance survives verification but the enumeration is materially wrong and would be destructive if applied verbatim. CONFIRMED: the invariant is real and explicit — Analysis/FabiusFunction/AGENTS.md line 36 lists "a doc comment on every non-`private` declaration" under "Invariants that must not regress." All 14 quoted signatures match the ...

### Cluster: fourier-legendre

#### Four modules in this cluster violate the doc-comment invariant on 131 public declarations, and two have no module header at all

Confidence high.  `PeriodicFourier.lean:1`, `PeriodicFourier.lean:21`, `PeriodicMean.lean:1`, `PeriodicMean.lean:89`, `PeriodicRegularity.lean:67`

**Why.** This is a stated project invariant, not a style preference: AGENTS.md lists it alongside `no sorry` and `set_option autoImplicit false`. The `Periodic*` family accounts for essentially all of the violations in this cluster (131 of 134), and the two missing module headers make PeriodicFourier.lean in particular hard to navigate — its first 350 lines are about Mellin transforms of Bose kernels and the Riemann zeta function, which nothing in the file name or (absent) header announces. By contrast ...

**Proposal.** Six modules in this cluster violate the doc-comment invariant on 138 public declarations, and two lack a module header.

Corrected counts (strict reading, including `@[simp] lemma` written on the declaration line):
  PeriodicFourier.lean            54  (53 at column 0, plus `@[simp] lemma negativeLaplacePsiCircle_coe` at :1376)
  PeriodicRegularity.lean         41
  PeriodicMean.lean               22
  PeriodicSmooth.lean             18  (15 at column 0, plus `@[simp] lemma`s at :44, :57, :212)
  FabiusLegendreLeastSquares.lean  2  (:44, :430)
  LegendreSeriesConvergence.lean   1  (:416)

These are new-code regressions, not legacy debt: all four Periodic* modules were added on 2026-08-23 (commits 358614119, 5671191f3, 25de7d803, 25aba5507), so they violated the invariant at introduction. That is what makes this cluster the right place to fix, even though the gap is corpus-wide (968 undocumented declarations across 81 of 175 modules; 12 modules lack a `/-!` header -- also FabiusSaddleCentral, FabiusSaddleExponentAllOrders, FabiusSaddleReferenceTail, FabiusSaddleTailAllOrders, ...

**Verifier.** Every checkable assertion holds. (1) AGENTS.md states the invariant verbatim ("a doc comment on every non-`private` declaration"), and docs/COLLABORATION.md:308 restates it plus "accurate module headers". (2) All eight cited file:line anchors exist with the quoted signatures: PeriodicFourier.lean:21 `lemma ...

### Cluster: lambert-asymptotics

#### Roughly 115 public declarations in this cluster carry no doc comment, violating the stated project invariant

Confidence high.  `FabiusLambertAllOrderAlgebra.lean:39`, `FabiusLambertAllOrderAlgebra.lean:44`, `FabiusLambertAllOrderAlgebra.lean:60`, `FabiusLambertAllOrderAlgebra.lean:67`, `FabiusLambertAllOrderAlgebra.lean:79`

**Why.** `Analysis/FabiusFunction/AGENTS.md` lists "a doc comment on every non-`private` declaration" among the invariants that must not regress. I ran a scan over all 36 cluster modules for lines matching `(@[…])? (noncomputable)? (theorem|lemma|def|abbrev|structure|instance)` whose immediately preceding non-attribute line does not end in `-/`, and got ~115 hits. The gap is not uniform noise: FabiusLambertAllOrderAlgebra.lean documents its two definitions and none of its eleven theorems, and ...

**Proposal.** Roughly 120 public declarations across ten modules in this cluster carry no doc comment, violating the `Analysis/FabiusFunction/AGENTS.md` invariant "a doc comment on every non-`private` declaration".

Corrected location list: drop `SaddleLogAsymptoticTransfer.lean:148` — `HasBoundedPolynomialCoefficients` already carries a doc comment at lines 146-147. The remaining 35 cited locations are all genuine. Replace the second `current` example with an actually-undocumented public definition from that file, e.g. `SaddleLogAsymptoticTransfer.lean:334`:

    def realLogTaylor (N : ℕ) (u : ℝ) : ℝ :=
      ∑ j ∈ Finset.range N,
        PowerSeries.coeff j (PowerSeries.log ℝ) * u ^ j

Corrected per-file counts (verified by scanning declaration lines against preceding `/-- … -/`):
- FabiusLogMainDefect.lean — 37 (53 declarations, 0 private, 16 doc comments)
- SaddleLogAsymptoticTransfer.lean — 33 (36 declarations, exactly 3 doc comments, at lines 146, 510, 587), NOT 28
- FabiusLambertDerivativeBounds.lean — 19
- FabiusLambertAllOrderAlgebra.lean — 11 of 15 public declarations (the file ...

**Verifier.** The core claim survives direct inspection, but one cited location and several supporting numbers are wrong.

CONFIRMED (35 of 36 cited locations). `Analysis/FabiusFunction/AGENTS.md` really does list "a doc comment on every non-`private` declaration" among the "Invariants that must not regress". I opened every cited file:line. 35 of the 36 are ...

### Cluster: negative-laplace

#### 145 non-`private` declarations in 13 of the 20 cluster modules carry no doc comment, and two modules have no module header at all — a direct violation of the stated invariant

Confidence high.  `NegativeLaplaceVerticalTaylor.lean:27`, `NegativeLaplaceVertical.lean:33`, `NegativeLaplaceDerivativeBounds.lean:24`, `NegativeLaplaceVerticalFourthBound.lean:17`, `NegativeLaplaceVerticalFourthBound.lean:4`

**Why.** This is the one invariant in AGENTS.md that is measurably regressed in this cluster, and the undocumented set is not marginal: it includes the four public definitions `negativeLaplaceKernelFirst/Second/Third/Fourth` and their complex counterparts, the entire `negativeLaplaceDyadicFactor` product API, all of `StieltjesConstant.lean`'s zeta interface, and 37 declarations in `NegativeLaplaceVerticalTaylor.lean`. Calling a 570-line module with a dozen exported definitions "scratch development" ...

**Proposal.** The finding stands, but its scope must be narrowed to the current working tree (HEAD 5cecb3e41 plus uncommitted changes), because commit 4c59369fe and an in-flight edit already landed part of it.

ALREADY DONE — do not redo: the NegativeLaplaceVerticalFourthBound.lean header has been replaced with a 45-line one that already documents the four complex kernel derivatives, the dilation recurrences, `‖negativeLaplaceVerticalKernelLogFourth s θ‖ ≤ 1542` for `s ≥ 1`, and the dyadic/`rpow`/Lambert-radius estimates; `/-! # … -/` module headers now exist in NegativeLaplaceVerticalOrdinaryJets.lean (line 4) and GammaSecondOrder.lean (line 7); all 27 NegativeLaplaceVertical.lean declarations now carry doc comments (uncommitted).

STILL OUTSTANDING — 118 non-`private` declarations lacking a doc comment, per file: NegativeLaplaceVerticalTaylor 37, NegativeLaplaceDerivativeBounds 17, NegativeLaplaceVerticalFourthBound 17, BoseFinitePartIntegral 13, StieltjesConstant 11, NegativeLaplaceVerticalAllOrderBound 6, MellinBose 6, NegativeLaplaceVerticalSmooth 4, NegativeLaplaceVerticalOrdinaryJets 3, ...

**Verifier.** Every claim checks out against the commit the audit was run on (768357067, the HEAD in my session snapshot). I verified each citation with `git show 768357067:<path>`: (1) NegativeLaplaceVerticalFourthBound.lean lines 4-8 read verbatim "# A uniform off-axis fourth derivative bound" / "Scratch development for the fourth vertical logarithmic ...

### Cluster: papers-aggregates

#### `proposition_twenty_two` has no doc comment, and the doc comment above `proposition_twenty_two_initial` describes the recurrences it does not state

Confidence high.  `PaperStatements.lean:740`, `PaperStatements.lean:741`, `PaperStatements.lean:744`

**Why.** Two defects in one place. First, `proposition_twenty_two` is the only public declaration in `PaperStatements.lean` with no doc comment, violating the stated project invariant that every non-private declaration carries one (mechanically confirmed by scanning every `theorem`/`lemma`/`def` in the cluster for a preceding `-/`). Second, the docstring that is present sits on `proposition_twenty_two_initial`, whose statement is `moment 0 = 1 ∧ halfMoment 0 = 1` — the initial conditions, not "the ...

**Proposal.** Finding stands; adjust only the severity framing and add a follow-up step.

Split the doc comment so each sits on the declaration it describes:

/-- Proposition 22, initial values: `c_0 = d_0 = 1`. -/
theorem proposition_twenty_two_initial : moment 0 = 1 ∧ halfMoment 0 = 1

/-- Proposition 22: the Bernoulli recurrences for `c_n` and `d_n`, valid for
`n ≥ 1`. -/
theorem proposition_twenty_two (n : ℕ) (hn : 1 ≤ n) : ...

Framing correction: `proposition_twenty_two` does not "violate" a currently-held invariant. docs/DOCUMENTATION_AUDIT.md:94 records that roughly a third of public declarations corpus-wide have no doc comment, and states the invariant is deliberately enforced as a ratchet rather than as a property that holds today. The accurate statement is that this is the last remaining gap in PaperStatements.lean (doc_audit.py reports exactly one, and doc_audit_baseline.json records "PaperStatements.lean": 1), and that it sits in the highest-priority bucket the audit itself defines — "suggested order of work" item 3, doc comments on public declarations appearing in PAPER_COVERAGE.md, ...

**Verifier.** Every refutation route confirmed the finding. (1) Locations exact: PaperStatements.lean:740 is the doc comment, :741 is `proposition_twenty_two_initial`, :744 is `proposition_twenty_two`. (2) No math misquoted — the elided portions of the quoted signature match the file. (3) Both defects confirmed by the corpus's OWN tooling, not by eyeball: ...

#### Three public lemmas in the cluster have no doc comment, violating the project invariant

Confidence high.  `OriginalPaperSupplement.lean:225`, `OriginalPaperSupplement.lean:293`, `DraftCounterexamples.lean:91`

**Why.** The project invariant requires a doc comment on every non-private declaration. Scanning every `theorem`/`lemma`/`def`/`abbrev` in the eight cluster modules against the preceding line, exactly four declarations lack one; three are these (the fourth is `proposition_twenty_two`, reported separately). All three are `lemma` without `private`, so they are exported into the `Fabius` namespace and appear in generated documentation with an empty description.

**Proposal.** Add the three doc comments as proposed (the prose is accurate as written), but restate the finding as clearing three rows of a tracked backlog rather than as a newly discovered invariant breach.

Corrected statement: `centeredDyadic_mem_Icc` (OriginalPaperSupplement.lean:225), `centeredDyadic_mem_Ioo_of_odd` (:293) and `paperProxyTerm_pos` (DraftCounterexamples.lean:91) are three of the 862 undocumented public declarations already recorded in Analysis/FabiusFunction/docs/doc_audit_baseline.json ("OriginalPaperSupplement.lean": 2, "DraftCounterexamples.lean": 1). Both modules are near-clean and paper-facing, so they are cheap and high-value to finish.

Drop from the finding: the claim that the three "stand out as unintentionally public" (undocumented-public is 31% of this corpus by the project's own measurement, and the adjacent `private` helpers imply nothing), and the `private` alternative -- all three are the natural range/positivity facts for public `centeredDyadic` and public `paperProxyTerm` and should stay public.

Fix the usage line numbers: centeredDyadic_mem_Icc at :267 and ...

**Verifier.** Core survives direct verification, but the framing and three cited details are wrong. CONFIRMED: all three declarations exist at exactly the cited lines with signatures quoted verbatim (OriginalPaperSupplement.lean:225, :293; DraftCounterexamples.lean:91); none has a preceding doc comment (lines 224/292/90 are blank); none is private; both files ...

## Refuted candidates

Proposed by an auditor and killed by the verifier.  Listed so a later pass
does not re-propose them.

- core/weaken-hypothesis: `fabiusDyadic_cast_extended_formula` carries an unnecessary bound and a 40-line proof that a later theorem in the same file supersedes — Declarations verified: GlobalDyadic.lean:56 `fabiusDyadic_cast_extended_formula`, GlobalDyadic.lean:299 `fabiusDyadic_cast_extended_nat`, ...
- core/deduplicate: Three private lemmas are declared verbatim in both DyadicClosedForm.lean and FabiusUniformSpline.lean, which imports it — The finding is stale and factually wrong at every cited location; the deduplication it proposes has already been performed in the corpus, and its proposed edit ...
- core/documentation: The `Fabius.Existence` namespace violates the project's doc-comment invariant on 52 of its 55 public declarations — REFUTED on three independent grounds; the cited lines are real but every distinguishing claim fails.

(1) Proposal option (b) is factually false and would break ...
- regularity/new-corollary: Convexity's module header promises `F'(1/2) = 2` and that it is the global maximum; neither is stated anywhere — The claim's grep was for a surface syntactic form, not for the mathematics, and all three proposed theorems already exist in the corpus as k = 1 instances of ...
- dyadic/deduplicate: `thueMorseSign_block_concat` and the two block-decomposition sum lemmas are copied verbatim into three modules — STALE — the proposed deduplication has already been performed and committed; the finding was generated against a pre-affa557d2 revision of the tree.

(1) Cited ...
- dyadic/deduplicate: `Odd (2 * halfMoment n).den` is established twice by two unrelated inductions — REFUTED. Both declarations exist as quoted (HalfMomentDenominator.lean:33-34, TwoAdic.lean:209-210) with accurate signatures, and the import legality claim checks out (HalfMomentDenominator -> Normali
- thuemorse-qbinomial/deduplicate: The seven `thueMorseCentered*` lemmas are the `c = 0` instances of the `thueMorseTranslated*` lemmas, with byte-identical proof bodies — All 14 cited declarations exist at the cited lines with correctly quoted signatures, and the c=0 specialization is mathematically ...
- thuemorse-qbinomial/documentation: Three cluster modules have no module header, ~57 public declarations in the cluster have no doc comment, and `qBinomialFabiusGlobalSummand_zero_polynomial` is a misnamed redundant `@[simp]` lemma — The finding's headline assertion is flatly false at HEAD and was ...
- moments-probability/documentation: 114 public declarations in this cluster have no doc comment, including two public `noncomputable def`s — The arithmetic survives but the finding is redundant and its rationale is inverted.

VERIFIED TRUE: all 9 cited locations are exact and carry no doc comment ...
- fourier-legendre/weaken-hypothesis: The explicit Fabius-value Legendre formulas are stated only for the canonical fabius although their proofs are generic in (F, hF) — Locations and signatures are quoted accurately (FabiusTranslatedLegendreSeries.lean:107/151/174/195, ...
- fourier-legendre/weaken-hypothesis: The Legendre coefficient decay bound does not need 1 ≤ m — Declaration confirmed verbatim at LegendreSeriesConvergence.lean:337 (no misquote), and the boundary test does NOT falsify it: at m = 0 the conclusion is ((0:N):R)^3 * |c_0| = 0 <= 3*B, immediate from
- negative-laplace/new-corollary: The cumulants `negativeLaplaceLogFirst … Fourth` do not depend on `F`: the identification with `negativeLaplaceLogOrdinaryDeriv` is used inline but never stated — REFUTED on ground 5 (already present under another name), twice over, and the stated motivation is ...
- negative-laplace/weaken-hypothesis: `norm_negativeLaplaceVerticalKernel_le` hard-codes `N = 2`; the same proof gives arbitrary even order `2 * m`, which is what the module header advertises — REFUTED as redundant (criterion 5) and as resting on a factually false motivation.

Locations check out: ...
- negative-laplace/deduplicate: The interval-remainder estimate for the vertical logarithm is proved twice, once for general order and once for order three, with a verbatim-shared `|θ - t| ≤ |θ|` helper — Refuted on check 5 (already present under another name), plus two verifiable misstatements in ...
- negative-laplace/documentation: `norm_iteratedDeriv_negativeLaplaceVerticalKernelLogFirst_le`'s docstring claims a strip restriction `|theta| ≤ 1` that the statement does not impose — REFUTED — the finding is stale: the exact change it proposes has already been made and is committed in HEAD. The ...
- saddle/expose-private: A Fabius-free `IsBigO` form of the quantitative-saddle endpoint is private inside a Fabius module — REFUTED as redundant, mis-cited, and over-hypothesized.

(1) Already present under another name (the decisive point). ...
- saddle/documentation: Five cluster modules have no module header and two have essentially no declaration doc comments at all — The headline claim is factually false and one proposal rests on an invented quotation. (a) All five modules cited at :1 as "no module header" have substantial /-! headers ...
- saddle/new-corollary: The sharp Stirling bounds are never stated in filter form, and the weaker `O(log n)` theorem in the same file is proved independently rather than derived — REFUTED — the proposed corollary already exists in the corpus, and the finding's central factual premise ("the sharp ...
