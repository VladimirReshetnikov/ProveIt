import Mathlib

/-!
# Finite median mathematics: ambient Lean blueprint

STATUS: design scaffold, not a completed formalization.

This file contains definitions and records of proof obligations.  It introduces
no axioms and contains no `sorry`.  Constructing `FiniteMedianProofPackage` is
the ambient Lean milestone; the decisive iPRA endpoint is the derivation package
in `MedianObjectLanguageTarget.lean`.
-/

namespace MedianIPRAPlan

open scoped BigOperators

/-! ## Exact finite samples -/

/-- Number of entries strictly below `t`. -/
def countLT (xs : List ℚ) (t : ℚ) : ℕ :=
  (xs.filter fun x => x < t).length

/-- Number of entries strictly above `t`. -/
def countGT (xs : List ℚ) (t : ℚ) : ℕ :=
  (xs.filter fun x => t < x).length

/-- Division-free balance definition of a median. -/
def BalanceMedian (xs : List ℚ) (t : ℚ) : Prop :=
  xs ≠ [] ∧ 2 * countLT xs t ≤ xs.length ∧ 2 * countGT xs t ≤ xs.length

/-- A sorted copy is a certificate, not an appeal to a choice principle. -/
structure OrderedCopy (xs : List ℚ) where
  data : List ℚ
  perm : data.Perm xs
  sorted : data.Pairwise (· ≤ ·)

/-- Lower and upper middle indices, using zero-based indexing. -/
def lowerIndex (n : ℕ) : ℕ := (n - 1) / 2

def upperIndex (n : ℕ) : ℕ := n / 2

/-- Totalized order-statistic projections.  Nonempty hypotheses make the
relevant indices in range. -/
def lowerMiddle {xs : List ℚ} (o : OrderedCopy xs) : ℚ :=
  o.data.getD (lowerIndex xs.length) 0

def upperMiddle {xs : List ℚ} (o : OrderedCopy xs) : ℚ :=
  o.data.getD (upperIndex xs.length) 0

/-- Division-free conventional median: `M` is twice the median. -/
def TwiceMedian (xs : List ℚ) (M : ℚ) : Prop :=
  ∃ o : OrderedCopy xs,
    M = lowerMiddle o + upperMiddle o

/-- Sum of absolute deviations. -/
def absDev (xs : List ℚ) (t : ℚ) : ℚ :=
  (xs.map fun x => |x - t|).sum

/-! ## Finite rational laws -/

/-- A finite rational-valued law with natural multiplicity weights. -/
structure FinLaw where
  card : ℕ
  value : Fin card → ℚ
  weight : Fin card → ℕ
  total : ℕ
  total_pos : 0 < total
  weight_sum : (∑ i, weight i) = total

namespace FinLaw

def massLT (L : FinLaw) (t : ℚ) : ℕ :=
  ∑ i, if L.value i < t then L.weight i else 0

def massGT (L : FinLaw) (t : ℚ) : ℕ :=
  ∑ i, if t < L.value i then L.weight i else 0

def IsMedian (L : FinLaw) (t : ℚ) : Prop :=
  2 * L.massLT t ≤ L.total ∧ 2 * L.massGT t ≤ L.total

def moment1Num (L : FinLaw) : ℚ :=
  ∑ i, (L.weight i : ℚ) * L.value i

def moment2Num (L : FinLaw) : ℚ :=
  ∑ i, (L.weight i : ℚ) * (L.value i)^2

def mean (L : FinLaw) : ℚ := L.moment1Num / L.total

def variance (L : FinLaw) : ℚ :=
  L.moment2Num / L.total - (L.mean)^2

def absRisk (L : FinLaw) (t : ℚ) : ℚ :=
  ∑ i, (L.weight i : ℚ) * |L.value i - t|

/-- Cleared form of `|mean - median| ≤ standard deviation` when `M = 2m`.
No square root or division occurs in this predicate. -/
def MeanMedianBoundCleared (L : FinLaw) (M : ℚ) : Prop :=
  (2 * L.moment1Num - M * L.total)^2 ≤
    4 * ((L.total : ℚ) * L.moment2Num - L.moment1Num^2)

end FinLaw

/-! ## Exact odd sample-median laws -/

/-- Multinomial numerator for an odd sample median to equal support point `j`.
The intended support is strictly increasing and `weight` supplies masses. -/
def oddMedianPMFNumerator (weight : List ℕ) (j n : ℕ) : ℕ :=
  let N := 2 * n + 1
  let A := (weight.take j).sum
  let B := weight.getD j 0
  let C := (weight.drop (j + 1)).sum
  ∑ i ∈ Finset.range (n + 1),
    ∑ k ∈ Finset.range (n + 1),
      let h := N - i - k
      if 0 < h then
        (Nat.factorial N / (Nat.factorial i * Nat.factorial h * Nat.factorial k)) *
          A^i * B^h * C^k
      else 0

/-- Binomial-tail numerator for `P(sample median ≤ support[j])`. -/
def oddMedianCDFNumerator (weight : List ℕ) (j n : ℕ) : ℕ :=
  let N := 2 * n + 1
  let A := (weight.take (j + 1)).sum
  let W := weight.sum
  ∑ r ∈ Finset.Icc (n + 1) N,
    Nat.choose N r * A^r * (W - A)^(N - r)

/-! ## Median-derived estimators -/

/-- Pairwise slopes used by the Theil-Sen estimator. -/
def pairSlopes (pts : List (ℚ × ℚ)) : List ℚ :=
  (pts.zipIdx.flatMap fun p =>
    pts.zipIdx.filterMap fun q =>
      if p.2 < q.2 ∧ p.1.1 ≠ q.1.1 then
        some ((q.1.2 - p.1.2) / (q.1.1 - p.1.1))
      else none)

/-- Walsh averages for the Hodges-Lehmann estimator. -/
def walshAverages (xs : List ℚ) : List ℚ :=
  (xs.zipIdx.flatMap fun p =>
    xs.zipIdx.filterMap fun q =>
      if p.2 ≤ q.2 then some ((p.1 + q.1) / 2) else none)

/-! ## Proof package to construct -/

/-- Every field is a concrete theorem proved in the manuscript.  The record is
used only to make the formalization endpoint explicit. -/
structure FiniteMedianProofPackage where
  orderedCopy_exists :
    ∀ xs : List ℚ, ∃ o : OrderedCopy xs, True

  balance_iff_middle_interval :
    ∀ {xs : List ℚ} (hne : xs ≠ []) (o : OrderedCopy xs) (t : ℚ),
      BalanceMedian xs t ↔ lowerMiddle o ≤ t ∧ t ≤ upperMiddle o

  twiceMedian_exists_unique :
    ∀ {xs : List ℚ}, xs ≠ [] → ∃! M, TwiceMedian xs M

  absDev_minimizers :
    ∀ {xs : List ℚ} (hne : xs ≠ []) (o : OrderedCopy xs) (t : ℚ),
      (∀ a, absDev xs t ≤ absDev xs a) ↔
        lowerMiddle o ≤ t ∧ t ≤ upperMiddle o

  monotone_transport :
    ∀ {xs : List ℚ} {f : ℚ → ℚ},
      StrictMono f → ∀ t, BalanceMedian xs t →
        BalanceMedian (xs.map f) (f t)

  weighted_median_exists :
    ∀ L : FinLaw, ∃ t, L.IsMedian t

  weighted_absRisk_minimizers :
    ∀ (L : FinLaw) (t : ℚ),
      L.IsMedian t ↔ ∀ a, L.absRisk t ≤ L.absRisk a

  mean_median_bound_cleared :
    ∀ (L : FinLaw) (t : ℚ), L.IsMedian t →
      L.MeanMedianBoundCleared (2 * t)

  rank_replacement_lower :
    ∀ (xs ys : List ℚ) (r k : ℕ),
      xs.length = ys.length →
      (xs.zip ys).countP (fun p => p.1 ≠ p.2) ≤ r →
      r ≤ k →
      True  -- replace by the lower order-statistic inequality

  rank_replacement_upper :
    ∀ (xs ys : List ℚ) (r k : ℕ),
      xs.length = ys.length →
      (xs.zip ys).countP (fun p => p.1 ≠ p.2) ≤ r →
      k + r < xs.length →
      True  -- replace by the upper order-statistic inequality

  exact_odd_sample_law : Prop
  finite_jensen_for_C_functions : Prop
  median_filter_majority_interval : Prop
  theil_sen_collinear_recovery : Prop
  hodges_lehmann_symmetry : Prop
  conditional_median_L1_optimality : Prop
  one_dimensional_k_medians_update : Prop

/-! ## Effective analytic extension -/

/-- Regular rational interval name for a real number. -/
structure Regular where
  lo hi : ℕ → ℚ
  ordered : ∀ p, lo p ≤ hi p
  nestedLo : Monotone lo
  nestedHi : Antitone hi
  width : ∀ p, hi p - lo p ≤ (1 : ℚ) / 2^p

/-- These are not finite-list theorems.  A completed construction must provide
primitive-recursive interval evaluators and explicit moduli. -/
structure AnalyticMedianExtension where
  expMedian : Prop
  weibullMedian : Prop
  powerLawMedian : Prop
  sampleMedianEffectiveCLT : Prop
  normalEfficiencyLimit : Prop
  geometricMedianApproximation : Prop
  centerpointCertificate : Prop

end MedianIPRAPlan
