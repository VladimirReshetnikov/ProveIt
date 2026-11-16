import Mathlib

/-!
# Finite constructive central-limit blueprint

STATUS: uncompiled design file, not a completed formalization.

This file deliberately contains no `sorry` and introduces no theorem axiom.
The structures at the end package the proof obligations that a completed
ambient Lean development must instantiate.  The internal iPRA endpoint is in
`ObjectLanguageTarget.lean`.

The mathematical manuscript proves the obligations for finite rational laws.
The recommended implementation order is recorded in `ROADMAP.md`.
-/

namespace CentralLimitIPRAPlan

open scoped BigOperators

/-- A finite rational law.  `weightSum` makes every probability an exact
rational finite sum. -/
structure FinLaw where
  card : ℕ
  value : Fin card → ℚ
  weight : Fin card → ℕ
  total : ℕ
  total_pos : 0 < total
  weight_sum : (∑ i, weight i) = total

namespace FinLaw

/-- Exact expectation of a rational-valued observable. -/
def expect (L : FinLaw) (f : Fin L.card → ℚ) : ℚ :=
  (∑ i, (L.weight i : ℚ) * f i) / L.total

/-- Mean. -/
def mean (L : FinLaw) : ℚ := L.expect L.value

/-- Variance. -/
def variance (L : FinLaw) : ℚ :=
  L.expect (fun i => (L.value i - L.mean) ^ 2)

/-- Third absolute centered moment. -/
def thirdAbs (L : FinLaw) : ℚ :=
  L.expect (fun i => |L.value i - L.mean| ^ 3)

/-- Exact finite CDF at a rational threshold. -/
def cdf (L : FinLaw) (q : ℚ) : ℚ :=
  L.expect (fun i => if L.value i ≤ q then 1 else 0)

/-- A product-space outcome index.  A completed development should use this
or an equivalent mixed-radix code to define exact independence. -/
def ProdIdx (A B : FinLaw) := Fin A.card × Fin B.card

end FinLaw

/-- A regular interval name for a real: nested rational intervals of width at
most `2^-p`.  All analytic constants and functions in the internal proof are
represented in this form, not by arbitrary `Real` values. -/
structure Regular where
  lo hi : ℕ → ℚ
  ordered : ∀ p, lo p ≤ hi p
  nestedLo : Monotone lo
  nestedHi : Antitone hi
  width : ∀ p, hi p - lo p ≤ (1 : ℚ) / 2 ^ p

/-- Complex regular name as a pair of regular real names. -/
structure CRegular where
  re : Regular
  im : Regular

/-- Interface to the constructive analytic library required by the proof.
A finished implementation constructs this from finite Taylor sums, bisection,
Machin-type pi sums, and finite Riemann sums. -/
structure AnalyticNames where
  sqrtName : ℚ → Regular
  expName : Regular → Regular
  sinName cosName : Regular → Regular
  piName : Regular
  normalCDF : Regular → Regular
  normalDensityMax : ℚ
  normalDensityMax_le : normalDensityMax ≤ 2 / 5

/-- Mathematical row data after centering.  In the actual arithmetic checker,
all lists are Gödel-coded and all folds are primitive recursive. -/
structure CenteredRow where
  count : ℕ
  law : Fin count → FinLaw
  centered : ∀ j, (law j).mean = 0

namespace CenteredRow

/-- Exact total variance of a finite centered row. -/
def totalVariance (R : CenteredRow) : ℚ :=
  ∑ j, (R.law j).variance

/-- Exact sum of centered absolute third moments. -/
def totalThirdAbs (R : CenteredRow) : ℚ :=
  ∑ j, (R.law j).thirdAbs

end CenteredRow

namespace Regular

/-- Precision-wise enclosure of `|x-y| ≤ e`.  The extra dyadic term absorbs
endpoint widths.  A completed development will also prove equivalence with
its preferred regular-real order relation. -/
def absDiffLe (x y e : Regular) : Prop :=
  ∀ p,
    x.hi (p + 2) - y.lo (p + 2) ≤ e.hi p + (1 : ℚ) / 2 ^ p ∧
    y.hi (p + 2) - x.lo (p + 2) ≤ e.hi p + (1 : ℚ) / 2 ^ p

end Regular

/-- Semantic finite-array specification at rational thresholds.  `cdf q` is
the exact finite probability embedded as a constant regular name; `gaussian q`
is the standard-normal CDF name; `error q` is the displayed Berry--Esseen
majorant.  The raw rational threshold keeps the event decidable even when the
standard deviation is irrational. -/
def BerryEsseenSpec
    (cdf gaussian error : ℚ → Regular) : Prop :=
  ∀ q : ℚ, Regular.absDiffLe (cdf q) (gaussian q) (error q)

/-- The core proof obligations in ambient Lean.  This is a record to be
constructed, not an axiom asserting the central limit theorem. -/
structure FiniteCLTProofPackage where
  names : AnalyticNames

  /-- Exact finite probability algebra: product weights, expectation of sums,
  variance additivity, and characteristic-function factorization. -/
  finiteProbabilityAlgebra : Prop

  /-- Constructive Esseen smoothing inequality with kernel
      v_T(x) = (1-cos(Tx))/(pi*T*x^2)
  and explicit constant 24. -/
  esseenSmoothing : Prop

  /-- Bounded finite-array theorem: if total variance is one and every
  centered summand is bounded by b, then d_K ≤ min(1, 7 b). -/
  boundedArraySeven : Prop

  /-- Finite triangular-array Berry--Esseen theorem:
      d_K ≤ min(1, 64 * sum E|X_j|^3 / s^3). -/
  berryEsseenSixtyFour : Prop

  /-- Quantitative Lindeberg truncation theorem:
      L(eta) ≤ lambda^3, lambda ≤ 1/2
      implies d_K ≤ 28 eta + 3 lambda. -/
  lindebergQuantitative : Prop

  /-- Object-level representation and QF-induction proof are intentionally
  not fields here; they belong to `ObjectLanguageTarget.lean`. -/

/-- Corollary inventory to be implemented after the core package. -/
structure CorollaryPackage (core : FiniteCLTProofPackage) where
  iidBerryEsseen : Prop
  effectiveFiniteVarianceIID : Prop
  lyapunov : Prop
  deMoivreLaplaceGlobal : Prop
  deMoivreLaplaceLocal : Prop
  multivariateRationalProjections : Prop
  randomNumberOfSummands : Prop
  boundedMDependent : Prop
  finiteTreeMartingale : Prop
  multiplicativeLognormal : Prop
  latticeLocalLimit : Prop

/-!
A completed ambient theorem may use `Real` as a convenient semantic model,
but the decisive endpoint is stronger: compile every regular-name evaluator
and every finite checker to `PR`, prove its universal zero equation in
`PRAAx`, and only then transfer with `pra_iff_native`.
-/

end CentralLimitIPRAPlan
