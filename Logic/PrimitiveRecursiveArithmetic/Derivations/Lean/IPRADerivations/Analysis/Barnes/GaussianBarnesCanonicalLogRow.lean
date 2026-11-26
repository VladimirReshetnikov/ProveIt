import IPRADerivations.Analysis.Barnes.BarnesCutoff
import IPRADerivations.Analysis.Logarithm.GaussianLocalLogarithmName
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDifferenceQuotient

/-!
# The original cubic Barnes logarithm on rational disks

The Barnes factor logarithm is the original degree-three Mercator tail
at z/(B k), multiplied by k. Its finite sums stay within
2 R³/(3 k²) on the rational disk |z/B| ≤ R. The original signed
dyadic observation has an additional explicit 2 k/2^(p+4) error.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogRow

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (normSq scale series)
open DyadicComplexLogarithm (observation observationError precision unit)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianRationalHorner (ofGaussian ofGaussian_represents qmul represents_congr positive_product)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded qsub)
open GaussianRationalReciprocal (bounded_product)
open GaussianRationalSyntheticDivision (rescale_to)
open LogarithmRemainder (denominator denominator_positive)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "nativeBound" => ComplexLogarithmRemainder.bounded

def source (z R B k : PTm n) : Fm PTm n :=
  le one B ⋏ (le one k ⋏ (nativeBound z (R*B) ⋏ le (two*R) k))

def boundNumerator (R : PTm n) : PTm n := two*R*R*R
def boundDenominator (k : PTm n) : PTm n := num 3*k*k

def cubic (z N L : PTm n) : PTm n := ofGaussian (series z N L) (denominator N L)

def roundedCubic (p z R N : PTm n) : PTm n := ofGaussian (observation p z R N) (unit p)

def finiteValue (z B k L : PTm n) : PTm n := qmul (radiusPoint k one) (cubic z (B*k) L)

def roundedValue (p z R B k : PTm n) : PTm n := qmul (radiusPoint k one) (roundedCubic p z (R*B) (B*k))

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B k : PTm n) :
    (source z R B k).subst σ =
      source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ k) := by simp [source,two,one]

@[simp] theorem subst_boundNumerator {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (boundNumerator R) = boundNumerator (Syn.subst σ R) := by simp [boundNumerator,two]

@[simp] theorem subst_boundDenominator {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (boundDenominator k) = boundDenominator (Syn.subst σ k) := by simp [boundDenominator]

@[simp] theorem subst_cubic {m : ℕ} (σ : Fin n → PTm m) (z N L : PTm n) :
    Syn.subst σ (cubic z N L) = cubic (Syn.subst σ z) (Syn.subst σ N) (Syn.subst σ L) := by simp [cubic]

@[simp] theorem subst_roundedCubic {m : ℕ} (σ : Fin n → PTm m) (p z R N : PTm n) :
    Syn.subst σ (roundedCubic p z R N) = roundedCubic (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ N) := by
  simp [roundedCubic]

@[simp] theorem subst_finiteValue {m : ℕ} (σ : Fin n → PTm m) (z B k L : PTm n) :
    Syn.subst σ (finiteValue z B k L) = finiteValue (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ L) := by
  simp [finiteValue,one]

@[simp] theorem subst_roundedValue {m : ℕ} (σ : Fin n → PTm m) (p z R B k : PTm n) :
    Syn.subst σ (roundedValue p z R B k) =
      roundedValue (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ k) := by
  simp [roundedValue,one]

theorem bound_denominator_positive (k : PTm n) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx] le one (boundDenominator k) :=
  positive_product _ _ (positive_product _ _ (le_of_eq_add (d := two) (by ipra_ring)) hk) hk

theorem local_source (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] GaussianLocalLogarithmName.source z (R*B) (B*k) :=
  .andI (positive_product B k h.andE₁ h.andE₂.andE₁) (.andI h.andE₂.andE₂.andE₁
    (le_congr (by ipra_ring) (mul_comm _ _) (mul_le_mul_right B h.andE₂.andE₂.andE₂)))

theorem cubic_bound (z R B k L : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] bounded (cubic z (B*k) L) (boundNumerator R) (boundDenominator k*k) := by
  let N := B*k
  let D := denominator N L
  let A := boundNumerator R
  let C := boundDenominator k*k
  let F := B*B*B
  let T := series z N L
  have hBk := local_source z R B k h
  have hC := positive_product (boundDenominator k) k (bound_denominator_positive k h.andE₂.andE₁) h.andE₂.andE₁
  have hF := positive_product _ _ (positive_product _ _ h.andE₁ h.andE₁) h.andE₁
  have hD := denominator_positive N L hBk.andE₁
  have native := ComplexLogarithmRemainder.canonical_bound z N (R*B) L hBk.andE₂.andE₁ hBk.andE₂.andE₂
  change Γ ⊢[PRAAx] le (normSq (scale (num 3*N*N*N) T)) ((two*(R*B)*(R*B)*(R*B)*D)*(two*(R*B)*(R*B)*(R*B)*D)) at native
  have scaled : Γ ⊢[PRAAx] le (F*(F*((C*C)*normSq T))) (F*(F*((A*A)*(D*D)))) :=
    le_congr ((ComplexLogarithmRemainder.normSq_scale (num 3*N*N*N) T).eqTrans
      (by dsimp only [N,C,F,boundDenominator]; ipra_ring))
      (by dsimp only [A,F,boundNumerator]; ipra_ring) native
  exact bounded_of_cleared _ _ _ _ _ hD hC (ofGaussian_represents T D hD)
    (RationalValueBounds.positive_cancel hF (RationalValueBounds.positive_cancel hF scaled))

theorem finite_bound (z R B k L : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] bounded (finiteValue z B k L) (boundNumerator R) (boundDenominator k) := by
  let A := boundNumerator R
  let D := boundDenominator k
  let c := radiusPoint k one
  let v := cubic z (B*k) L
  have hD := bound_denominator_positive k h.andE₂.andE₁
  have hE := positive_product D k hD h.andE₂.andE₁
  have raw := bounded_product c v k one A (D*k) (le_refl one) hE (radius_bounded k one (le_refl one))
    (cubic_bound z R B k L h)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_refl one) hE) hD
    (le_of_eq_add (d := zero) (by ipra_ring)) raw

theorem rounding_distance (p z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (roundedCubic p z R N) (cubic z N (precision p)) two (unit p) := by
  let D := denominator N (precision p)
  let U := unit p
  let O := observation p z R N
  let T := series z N (precision p)
  let E := U*D
  have hD := denominator_positive N (precision p) hN
  have hU := GaussianLocalLogarithmName.unit_positive (Γ := Γ) p
  have hE := positive_product U D hU hD
  have left := rescale_to (roundedCubic p z R N) O U D E (ofGaussian_represents O U hU) (.eqRefl _)
  have right := rescale_to (cubic z N (precision p)) T D U E (ofGaussian_represents T D hD) (mul_comm _ _)
  have rep : Γ ⊢[PRAAx] GaussianRationalHorner.represents
      (qsub (roundedCubic p z R N) (cubic z N (precision p))) (observationError p z R N) E := by
    simpa only [observationError, GaussianRootAlgebra.sub,D,U,O,T] using
      GaussianRationalMetric.qsub_represents _ _ _ _ _ hE left right
  exact bounded_of_cleared _ _ _ _ _ hE hU rep
    (le_congr (.eqRefl _) (by dsimp only [E,D,U]; ipra_ring)
      (mul_le_mul_right (U*U) (DyadicComplexLogarithm.observation_rounding p z R N hN) |>
        le_congr (mul_comm _ _) (mul_comm _ _)))

theorem rounded_error (p z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] distanceBounded (roundedValue p z R B k) (finiteValue z B k (precision p)) (two*k) (unit p) := by
  have hU := GaussianLocalLogarithmName.unit_positive (Γ := Γ) p
  have hBk := positive_product B k h.andE₁ h.andE₂.andE₁
  have raw := GaussianNamedDifferenceQuotient.scale_distance (radiusPoint k one)
    (roundedCubic p z (R*B) (B*k)) (cubic z (B*k) (precision p)) k two (unit p) hU
    (radius_bounded k one (le_refl one)) (rounding_distance p z (R*B) (B*k) hBk)
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _) (mul_comm _ _) (.eqRefl _) raw

theorem actual_finite_Barnes_logarithm_row_bound_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 0) (var 1) (var 2) (var 3) ⟶
        bounded (finiteValue (var 0) (var 2) (var 3) (var 4)) (boundNumerator (var 1)) (boundDenominator (var 3))) :=
  closeUniv 5 (.impI (finite_bound _ _ _ _ _ Prf.hyp0))

theorem actual_rounded_Barnes_logarithm_row_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 1) (var 2) (var 3) (var 4) ⟶ distanceBounded
        (roundedValue (var 0) (var 1) (var 2) (var 3) (var 4)) (finiteValue (var 1) (var 3) (var 4) (precision (var 0)))
        (two*var 4) (unit (var 0))) :=
  closeUniv 5 (.impI (rounded_error _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogRow
