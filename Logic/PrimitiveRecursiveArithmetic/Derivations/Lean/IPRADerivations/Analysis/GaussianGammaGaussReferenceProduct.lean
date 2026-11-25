import IPRADerivations.Analysis.GaussianGammaGaussReference
import IPRADerivations.Analysis.GaussianGammaGaussShiftedApartness

/-!
# The positive reference Gamma product in Gauss multiplication

The internal row (r) samples the original Gamma name at ((r+1)/m)
with radius one and denominator (m). The product has a uniform
precision schedule and an explicit separation denominator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussReferenceProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale oneCode)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaReciprocalInverse
  (gammaF gammaData gamma_regular lambdaDenominator lambdaNumerator lambda_positive actual_gamma_observation_bound)
open GaussianNameReciprocal (lower apart input)
open GaussianNamedFiniteProduct (rowBoundsAt rowDistance)
open GaussianNamedFiniteProductName (rowBounds rowRegular)
open GaussianNamedFiniteProductApartness (rowLower rowLowerAt)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def argument (r : PTm n) : PTm n := scale (succ r) oneCode

def rowValue (p r m : PTm n) : PTm n :=
  ap2 gammaF p (gammaData (argument r) one m m)

def rowBody : PTm 3 := rowValue (var 0) (var 1) (var 2)
def rowF : PR 3 := PTm.toPR rowBody
def rowRadius (m : PTm n) : PTm n := lambdaDenominator one m+two
def rowDenominator : PTm n := GaussianGammaC9Bound.majorant one

def nameF : PR 2 := GaussianNamedFiniteProductName.nameF rowF
def data (m : PTm n) : PTm n := GaussianNamedFiniteProductName.data m (rowRadius m) one m
def clock (p m : PTm n) : PTm n := GaussianNamedFiniteProductName.clock m (rowRadius m) one p
def apartClock (m : PTm n) : PTm n := GaussianNamedFiniteProductApartness.apartClock m rowDenominator

@[simp] theorem subst_argument {l : ℕ} (σ : Fin n → PTm l) (r : PTm n) :
    Syn.subst σ (argument r) = argument (Syn.subst σ r) := by simp [argument]

@[simp] theorem subst_rowValue {l : ℕ} (σ : Fin n → PTm l) (p r m : PTm n) :
    Syn.subst σ (rowValue p r m) = rowValue (Syn.subst σ p) (Syn.subst σ r) (Syn.subst σ m) := by
  simp [rowValue,gammaData,GaussianGammaReciprocalInverse.gammaHeight,one]

@[simp] theorem subst_rowRadius {l : ℕ} (σ : Fin n → PTm l) (m : PTm n) :
    Syn.subst σ (rowRadius m) = rowRadius (Syn.subst σ m) := by simp [rowRadius,one,two]

@[simp] theorem subst_rowDenominator {l : ℕ} (σ : Fin n → PTm l) :
    Syn.subst σ (rowDenominator : PTm n) = rowDenominator := by simp [rowDenominator,one]

@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (m : PTm n) :
    Syn.subst σ (data m) = data (Syn.subst σ m) := by simp [data,one]

@[simp] theorem subst_clock {l : ℕ} (σ : Fin n → PTm l) (p m : PTm n) :
    Syn.subst σ (clock p m) = clock (Syn.subst σ p) (Syn.subst σ m) := by simp [clock,one]

@[simp] theorem subst_apartClock {l : ℕ} (σ : Fin n → PTm l) (m : PTm n) :
    Syn.subst σ (apartClock m) = apartClock (Syn.subst σ m) := by simp [apartClock]

theorem row_at (p r m : PTm n) : Γ ⊢[PRAAx] ap3 rowF p r m ≐ rowValue p r m := by
  change Γ ⊢[PRAAx] ConciseIPRA.PTm.app (PTm.toPR rowBody) ![p,r,m] ≐ _
  simpa only [rowBody,subst_rowValue,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using toPR_eq (Γ := Γ) rowBody ![p,r,m]

theorem row_source (r m : PTm n) (hr : Γ ⊢[PRAAx] lt r m) :
    Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source (argument r) one m one m :=
  GaussianGammaGaussReference.shifted_reference_source r m hr

theorem row_bound_at (p r m : PTm n) (hr : Γ ⊢[PRAAx] lt r m) :
    Γ ⊢[PRAAx] bounded (ap3 rowF p r m) (rowRadius m) one := by
  let L : PTm n := lambdaDenominator one m
  let N : PTm n := lambdaNumerator one one
  let U := unit p
  have h := row_source r m hr
  have raw : Γ ⊢[PRAAx] bounded (rowValue p r m) (L*U+two*N) (N*U) :=
    actual_gamma_observation_bound p (argument r) one m one m h
  have hN : Γ ⊢[PRAAx] le one N := (lambda_positive one one m (le_refl one) h.andE₂.andE₂.andE₁).andE₁
  have hU : Γ ⊢[PRAAx] le one U := unit_positive p
  exact bound_congr (row_at p r m).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ (positive_product _ _ hN hU) (le_refl one)
      (by change Γ ⊢[PRAAx] le ((L*U+two*N)*one) ((L+two)*(N*U))
          ipra_le 𝔞 L*𝔞 U*sl hN+2*𝔞 N*sl hU) raw)

theorem row_distance_at (p q r m : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx] distanceBounded
    (ap3 rowF p r m) (ap3 rowF q r m) (one*(unit p+unit q)) (unit p*unit q) := by
  have hf := gamma_regular (argument r) one m one m (row_source r m hr)
  have raw : Γ ⊢[PRAAx] distanceBounded (rowValue p r m) (rowValue q r m) (unit p+unit q) (unit p*unit q) :=
    GaussianNameEquivalence.point_at gammaF (gammaData (argument r) one m m) p q hf
  exact distance_congr (row_at p r m).eqSymm (row_at q r m).eqSymm
    (one_mul (unit p+unit q)).eqSymm (.eqRefl _) raw

theorem row_lower_at (p r m : PTm n) (hr : Γ ⊢[PRAAx] lt r m) :
    Γ ⊢[PRAAx] lower (ap3 rowF p r m) rowDenominator :=
  GaussianNameReciprocal.lower_congr (row_at p r m).eqSymm (.eqRefl _)
    (GaussianGammaGaussShiftedApartness.gamma_observation_lower p (argument r) one m one m (row_source r m hr))

theorem row_bounds (m : PTm n) : Γ ⊢[PRAAx] rowBounds rowF m (rowRadius m) m := by
  refine .allI (.allI (.impI ?_))
  let M := Syn.shift (Syn.shift m)
  let Δ := lt (var 0) M :: (Γ.map Fm.shift).map Fm.shift
  simpa [Δ,M,rowBounds,rowBoundsAt,Syn.shift] using
    row_bound_at (var 1) (var 0) M (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) M)

theorem row_regular (m : PTm n) : Γ ⊢[PRAAx] rowRegular rowF m one m := by
  refine .allI (.allI (.allI (.impI ?_)))
  let M := Syn.shift (Syn.shift (Syn.shift m))
  let Δ := lt (var 0) M :: ((Γ.map Fm.shift).map Fm.shift).map Fm.shift
  simpa [Δ,M,rowRegular,rowDistance,Syn.shift,one] using
    row_distance_at (var 2) (var 1) (var 0) M (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) M)

theorem row_lower (m : PTm n) : Γ ⊢[PRAAx] rowLower rowF m rowDenominator m := by
  refine .allI (.allI (.impI ?_))
  let M := Syn.shift (Syn.shift m)
  let Δ := lt (var 0) M :: (Γ.map Fm.shift).map Fm.shift
  simpa [Δ,M,rowLower,rowLowerAt,Syn.shift] using
    row_lower_at (var 1) (var 0) M (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) M)

theorem row_denominator_positive : Γ ⊢[PRAAx] le one (rowDenominator : PTm n) :=
  GaussianGammaGaussShiftedApartness.majorant_positive one (le_refl one)

theorem name_at (p m : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data m) ≐
    GaussianNamedFiniteProduct.sample rowF (clock p m) m m :=
  GaussianNamedFiniteProductName.name_at rowF p m (rowRadius m) one m

theorem name_regular (m : PTm n) : Γ ⊢[PRAAx] pointCN nameF (data m) :=
  GaussianNamedFiniteProductName.name_regular rowF m (rowRadius m) one m (row_bounds m) (row_regular m)

theorem name_lower (p m : PTm n) :
    Γ ⊢[PRAAx] lower (ap2 nameF p (data m)) (GaussianNamedFiniteProductApartness.denominator rowDenominator m) :=
  GaussianNamedFiniteProductApartness.name_lower rowF p m (rowRadius m) one rowDenominator m
    row_denominator_positive (row_lower m)

theorem name_apart (m : PTm n) : Γ ⊢[PRAAx] apart nameF (apartClock m) (data m) :=
  GaussianNamedFiniteProductApartness.name_apart rowF m (rowRadius m) one rowDenominator m
    row_denominator_positive (row_lower m)

theorem name_input (m : PTm n) : Γ ⊢[PRAAx] input nameF (apartClock m) (data m) :=
  .andI (name_regular m) (name_apart m)

theorem actual_Gauss_reference_product_input_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (input nameF (apartClock (var 0)) (data (var 0))) :=
  closeUniv 1 (name_input (var 0))

end LeanProofs.IPRA.Analysis.GaussianGammaGaussReferenceProduct
