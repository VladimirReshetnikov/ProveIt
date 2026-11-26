import IPRADerivations.Analysis.Trigonometry.GaussianSineProductImaginaryFirstOrderBound
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaCanonicalExponent
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate
import IPRADerivations.Analysis.Names.GaussianNamedDifference

/-!
# First-order estimate for the original cofinal imaginary sine product

The actual cofinal product and actual cofinal logarithmic-derivative
sum have one common finite cutoff. Transferring the uniform finite
estimate at this cutoff gives the named first-order estimate with no
remaining cutoff error.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryCofinalDerivative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast product_distance)
open GaussianNameBounds (U sample_bound)
open GaussianNameRingLaws (multiply_sample_error)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qadd qmul qmul_canonical)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalSyntheticDivision (qadd_sub_cancel qmul_congr)
open GaussianReconstructionRoots (distance_triangle)
open GaussianSineProductImaginaryFirstOrder (step)
open GaussianSineProductImaginaryFirstOrderBound (axis_disk bound finite_error productBound product_bound)
open GaussianSineProductImaginaryLogDerivative (axisNumerator derivative finite_logarithmic_derivative logarithmSum product)
open GaussianSineProductImaginaryLogDerivativeTail (rational_real_bound)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "sineF" => GaussianSineProductName.nameF
local notation "rowF" => GaussianSineProductImaginaryLogDerivativeTail.nameF
local notation "rowData" => GaussianSineProductImaginaryLogDerivativeTail.data

def sineData (A B R : PTm n) : PTm n := GaussianSineProductName.data (axisNumerator A) R B
def derivativeF : PR 2 := multiplyF sineF rowF
def derivativeData (A B R : PTm n) : PTm n := multiplyData sineF rowF (sineData A B R) (rowData A B R)
def incrementF : PR 2 := GaussianNamedDifference.nameF sineF sineF
def incrementData (A B C R : PTm n) : PTm n :=
  GaussianNamedDifference.data (sineData (A+C) B R) (sineData A B R)
def weightedF : PR 2 := multiplyF constantF derivativeF
def weightedData (A B C R : PTm n) : PTm n := multiplyData constantF derivativeF (step B C) (derivativeData A B R)

def source (A B C R : PTm n) : Fm PTm n := le one B ⋏ le (A+C) (R*B)
def cutoff (R p : PTm n) : PTm n :=
  GaussianSineProductName.cutoff R p+GaussianSineProductImaginaryLogDerivativeTail.cutoff R p

def derivativeCost (A B R : PTm n) : PTm n :=
  (multiplyModulus sineF rowF (sineData A B R) (rowData A B R)+one)+(U rowF (rowData A B R)+productBound R)

def weightedCost (A B C R : PTm n) : PTm n :=
  (multiplyModulus constantF derivativeF (step B C) (derivativeData A B R)+one)+R*derivativeCost A B R

def cost (A B C R : PTm n) : PTm n := num 8+weightedCost A B C R

@[simp] theorem subst_sineData {m : ℕ} (σ : Fin n → PTm m) (A B R : PTm n) :
    Syn.subst σ (sineData A B R) = sineData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ R) := by
  simp [sineData, GaussianSineProductName.data]

@[simp] theorem subst_derivativeData {m : ℕ} (σ : Fin n → PTm m) (A B R : PTm n) :
    Syn.subst σ (derivativeData A B R) = derivativeData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ R) := by
  simp [derivativeData]

@[simp] theorem subst_incrementData {m : ℕ} (σ : Fin n → PTm m) (A B C R : PTm n) :
    Syn.subst σ (incrementData A B C R) = incrementData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ R) := by
  simp [incrementData]

@[simp] theorem subst_weightedData {m : ℕ} (σ : Fin n → PTm m) (A B C R : PTm n) :
    Syn.subst σ (weightedData A B C R) = weightedData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ R) := by
  simp [weightedData]

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (A B C R : PTm n) :
    (source A B C R).subst σ = source (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ R) := by
  simp [source, one]

@[simp] private theorem subst_bound {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (bound R) = bound (Syn.subst σ R) := by
  simp [GaussianSineProductImaginaryFirstOrderBound.bound, GaussianSineProductImaginaryFirstOrderBound.exponent,
    GaussianSineProductImaginaryFirstOrderBound.forcingBound, GaussianSineProductImaginaryFirstOrderBound.derivativeBound,
    productBound, two]

@[simp] private theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (A B C R : PTm n) :
    Syn.subst σ (cost A B C R) = cost (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ R) := by
  simp [cost, weightedCost, derivativeCost, productBound, one, two]

private theorem sine_regular (A B R : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] pointCN sineF (sineData A B R) :=
  GaussianSineProductName.name_regular _ _ _ hB (axis_disk A B R hA)

theorem derivative_regular (A B R : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] pointCN derivativeF (derivativeData A B R) :=
  multiply_fast sineF rowF _ _ (sine_regular A B R hB hA)
    (GaussianSineProductImaginaryLogDerivativeTail.regular A B R hB hA)

private theorem sine_at_finite (A B R p N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le A (R*B)) (hN : Γ ⊢[PRAAx] le (cutoff R p) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 sineF p (sineData A B R)) (product A B N) one (unit p) :=
  distance_symmetric _ _ _ _ (unit_positive p)
    (GaussianSineProductName.cofinal_error _ R B p N hB (axis_disk A B R hA)
      (le_trans (le_add_right _ _) hN))

theorem derivative_at_finite (A B R p N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le A (R*B)) (hN : Γ ⊢[PRAAx] le (cutoff R p) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 derivativeF p (derivativeData A B R)) (derivative A B N)
      (derivativeCost A B R) (unit p) := by
  let x := sineData A B R
  let y := rowData A B R
  let P := product A B N
  let S := logarithmSum A B N
  let a := ap2 sineF p x
  let b := ap2 rowF p y
  let W := U rowF y+productBound R
  have hb := GaussianSineProductImaginaryLogDerivativeTail.regular A B R hB hA
  have hU := unit_positive (Γ := Γ) p
  have hS := distance_symmetric _ _ _ _ hU
    (GaussianSineProductImaginaryLogDerivativeTail.cofinal_error A B R p N hB hA
      (le_trans (le_add_left _ _) hN))
  have hd : Γ ⊢[PRAAx] distanceBounded (qmul a b) (derivative A B N) W (unit p) :=
    distance_congr (.eqRefl _) (finite_logarithmic_derivative A B N hB).eqSymm
      (by unfold W; ipra_ring) (.eqRefl _)
      (product_distance a P b S one one (unit p) (U rowF y) (productBound R) hU
        (sine_at_finite A B R p N hB hA hN) hS (sample_bound rowF y p hb) (product_bound A B R N hB hA))
  exact distance_triangle_same _ _ _ _ _ _ hU
    (multiply_sample_error sineF rowF x y p (sine_regular A B R hB hA) hb) hd

private theorem increment_at_finite (A B C R p N : PTm n) (h : Γ ⊢[PRAAx] source A B C R)
    (hN : Γ ⊢[PRAAx] le (cutoff R p) N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 incrementF p (incrementData A B C R)) (qsub (product (A+C) B N) (product A B N))
      (num 8) (unit p) := by
  let x := sineData (A+C) B R
  let y := sineData A B R
  have hA : Γ ⊢[PRAAx] le A (R*B) := le_trans (le_add_right _ _) h.andE₂
  have hU := unit_positive (Γ := Γ) p
  have read := GaussianNamedDifference.sample_error sineF sineF x y p
    (sine_regular (A+C) B R h.andE₁ h.andE₂) (sine_regular A B R h.andE₁ hA)
  have changeAt := GaussianNamedDifference.difference_distance
    (ap2 sineF p x) (product (A+C) B N) (ap2 sineF p y) (product A B N) one one (unit p) hU
    (sine_at_finite (A+C) B R p N h.andE₁ h.andE₂ hN) (sine_at_finite A B R p N h.andE₁ hA hN)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hU read changeAt)

private theorem weighted_at_finite (A B C R p N : PTm n) (h : Γ ⊢[PRAAx] source A B C R)
    (hN : Γ ⊢[PRAAx] le (cutoff R p) N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 weightedF p (weightedData A B C R)) (qmul (step B C) (derivative A B N))
      (weightedCost A B C R) (unit p) := by
  let z := derivativeData A B R
  let c := step B C
  let v := ap2 derivativeF p z
  let E := derivativeCost A B R
  have hA : Γ ⊢[PRAAx] le A (R*B) := le_trans (le_add_right _ _) h.andE₂
  have hC : Γ ⊢[PRAAx] le C (R*B) := le_trans (le_add_left _ _) h.andE₂
  have hr := derivative_regular A B R h.andE₁ hA
  have hU := unit_positive (Γ := Γ) p
  have hc : Γ ⊢[PRAAx] bounded c R one :=
    rational_real_bound _ _ R one h.andE₁ (le_refl one) (le_congr (one_mul _).eqSymm (.eqRefl _) hC)
  have first := distance_congr (.eqRefl _) (qmul_congr (constant_at p c) (.eqRefl v)) (.eqRefl _) (.eqRefl _)
    (multiply_sample_error constantF derivativeF c z p (constant_regular c) hr)
  have second : Γ ⊢[PRAAx] distanceBounded (qmul c v) (qmul c (derivative A B N)) (R*E) (unit p) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (product_distance c c v (derivative A B N) zero E (unit p) (U derivativeF z) R hU
        (distance_refl_zero c (unit p) hU) (derivative_at_finite A B R p N h.andE₁ hA hN)
        (sample_bound derivativeF z p hr) hc)
  exact distance_triangle_same _ _ _ _ _ _ hU first second

private theorem finite_increment_error (A B C R N : PTm n) (h : Γ ⊢[PRAAx] source A B C R) :
    Γ ⊢[PRAAx] distanceBounded (qsub (product (A+C) B N) (product A B N)) (qmul (step B C) (derivative A B N))
      ((C*C)*bound R) (B*B) := by
  let a := product (A+C) B N
  let b := product A B N
  let w := qmul (step B C) (derivative A B N)
  let D := B*B
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ h.andE₁ h.andE₁
  exact distance_congr (.eqRefl _) (qadd_sub_cancel b w (qmul_canonical _ _)) (by ipra_ring) (.eqRefl _)
    (GaussianNamedDifference.difference_distance a (qadd b w) b b _ zero D hD
      (finite_error A B C R N h.andE₁ h.andE₂) (distance_refl_zero b D hD))

theorem diagonal_at (A B C R p : PTm n) (h : Γ ⊢[PRAAx] source A B C R) :
    Γ ⊢[PRAAx] distanceBounded (ap2 incrementF p (incrementData A B C R)) (ap2 weightedF p (weightedData A B C R))
      (diagonalNumerator ((C*C)*bound R) (B*B) (cost A B C R) p) (diagonalDenominator (B*B) p) := by
  let N := cutoff R p
  let W := weightedCost A B C R
  let D := B*B
  let E := (C*C)*bound R
  let Uₚ := unit p
  have hU := unit_positive (Γ := Γ) p
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ h.andE₁ h.andE₁
  have a := increment_at_finite A B C R p N h (le_refl N)
  have b := finite_increment_error A B C R N h
  have c := distance_symmetric _ _ _ _ hU (weighted_at_finite A B C R p N h (le_refl N))
  have both := distance_triangle _ _ _ (num 8) Uₚ E D hU hD a b
  have joined := distance_triangle _ _ _ ((num 8)*D+E*Uₚ) (Uₚ*D) W Uₚ
    (positive_product _ _ hU hD) hU both c
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hU hD) hU)
    (positive_product _ _ hD hU)
    (le_of_eq_add (d := zero) (by dsimp only [diagonalDenominator, diagonalNumerator, cost, D, E, Uₚ, W]; ipra_ring))
    joined

theorem independent_rate (A B C R : PTm n) (h : Γ ⊢[PRAAx] source A B C R) :
    Γ ⊢[PRAAx] independentRate incrementF weightedF (incrementData A B C R) (weightedData A B C R) ((C*C)*bound R) (B*B) := by
  have hA : Γ ⊢[PRAAx] le A (R*B) := le_trans (le_add_right _ _) h.andE₂
  have hr := derivative_regular A B R h.andE₁ hA
  have hi := GaussianNamedDifference.name_regular sineF sineF (sineData (A+C) B R) (sineData A B R)
    (sine_regular (A+C) B R h.andE₁ h.andE₂) (sine_regular A B R h.andE₁ hA)
  have hw := multiply_fast constantF derivativeF (step B C) (derivativeData A B R) (constant_regular _) hr
  apply GaussianNamedLipschitzRate.independent_rate incrementF weightedF (incrementData A B C R) (weightedData A B C R)
    ((C*C)*bound R) (B*B) (cost A B C R)
    (positive_product _ _ h.andE₁ h.andE₁) hi hw
  refine .allI ?_
  let s (t : PTm n) := Syn.shift t
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (s A) (s B) (s C) (s R) := by
    simpa only [s, Fm.shift, Syn.shift, subst_source] using h.shift
  simpa only [diagonalEnvelope, Syn.shift, s, subst_incrementData, subst_weightedData, subst_cost, subst_bound, PTm.subst_mul]
    using diagonal_at (s A) (s B) (s C) (s R) (var 0) hs

theorem actual_cofinal_imaginary_sine_product_derivative_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let A := var 0
       let B := var 1
       let C := var 2
       let R := var 3
       source A B C R ⟶
       independentRate incrementF weightedF (incrementData A B C R) (weightedData A B C R) ((C*C)*bound R) (B*B)) :=
  closeUniv 4 (.impI (independent_rate _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryCofinalDerivative
