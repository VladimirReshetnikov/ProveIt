import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotient
import IPRADerivations.Analysis.FiniteOperations.GaussianBoundedInverseApartness

/-!
# An original divided difference with a genuinely named increment

The denominator uses the existing reciprocal-name program and its finite
apartness certificate. Multiplication by that very denominator cancels
to the original left-minus-right name. Its late native observations are
also proved nonzero, without selecting an abstract nonzero witness.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedIncrementDifferenceQuotient

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast multiply_equivalent)
open GaussianNameRingLaws (oneF one_fast multiply_associative multiply_commutative multiply_one_left)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_to_diagonal)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def nameF (F G K : PR 2) : PR 2 := multiplyF (GaussianNameReciprocal.nameF K) (GaussianNamedDifference.nameF F G)
def data (F G K : PR 2) (x y z a : PTm n) : PTm n :=
  multiplyData (GaussianNameReciprocal.nameF K) (GaussianNamedDifference.nameF F G)
    (GaussianNameReciprocal.nameData a z) (GaussianNamedDifference.data x y)
def input (F G K : PR 2) (x y z a : PTm n) : Fm PTm n :=
  pointCN F x ⋏ (pointCN G y ⋏ GaussianNameReciprocal.input K a z)
def leftData (F G K : PR 2) (x y z a : PTm n) : PTm n := multiplyData K (nameF F G K) z (data F G K x y z a)
def rightData (F G K : PR 2) (x y z a : PTm n) : PTm n := multiplyData (nameF F G K) K (data F G K x y z a) z
def nativeNumerator (K : PR 2) (a z t : PTm n) : PTm n := rawGaussian (GaussianNameReciprocal.tail K a z t)
def nativeDenominator (K : PR 2) (a z t : PTm n) : PTm n := rawDen (GaussianNameReciprocal.tail K a z t)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (F G K : PR 2) (x y z a : PTm n) :
    Syn.subst σ (data F G K x y z a) = data F G K (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ a) := by simp [data]
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (F G K : PR 2) (x y z a : PTm n) :
    (input F G K x y z a).subst σ = input F G K (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ a) := by simp [input]
@[simp] theorem subst_leftData {m : ℕ} (σ : Fin n → PTm m) (F G K : PR 2) (x y z a : PTm n) :
    Syn.subst σ (leftData F G K x y z a) = leftData F G K (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ a) := by simp [leftData]
@[simp] theorem subst_rightData {m : ℕ} (σ : Fin n → PTm m) (F G K : PR 2) (x y z a : PTm n) :
    Syn.subst σ (rightData F G K x y z a) = rightData F G K (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ a) := by simp [rightData]
@[simp] theorem subst_nativeNumerator {m : ℕ} (σ : Fin n → PTm m) (K : PR 2) (a z t : PTm n) :
    Syn.subst σ (nativeNumerator K a z t) = nativeNumerator K (Syn.subst σ a) (Syn.subst σ z) (Syn.subst σ t) := by simp [nativeNumerator]
@[simp] theorem subst_nativeDenominator {m : ℕ} (σ : Fin n → PTm m) (K : PR 2) (a z t : PTm n) :
    Syn.subst σ (nativeDenominator K a z t) = nativeDenominator K (Syn.subst σ a) (Syn.subst σ z) (Syn.subst σ t) := by simp [nativeDenominator]

theorem name_regular (F G K : PR 2) (x y z a : PTm n) (h : Γ ⊢[PRAAx] input F G K x y z a) : Γ ⊢[PRAAx]
    pointCN (nameF F G K) (data F G K x y z a) :=
  multiply_fast _ _ _ _
    (GaussianNameReciprocal.name_fast K a z h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂)
    (GaussianNamedDifference.name_regular F G x y h.andE₁ h.andE₂.andE₁)

theorem left_product (F G K : PR 2) (x y z a : PTm n) (h : Γ ⊢[PRAAx] input F G K x y z a) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF K (nameF F G K)) (GaussianNamedDifference.nameF F G)
      (leftData F G K x y z a) (GaussianNamedDifference.data x y) := by
  let J := GaussianNameReciprocal.nameF K
  let P := GaussianNamedDifference.nameF F G
  let u := GaussianNameReciprocal.nameData a z
  let v := GaussianNamedDifference.data x y
  have hk := h.andE₂.andE₂.andE₁
  have ha := h.andE₂.andE₂.andE₂
  have hj : Γ ⊢[PRAAx] pointCN J u := GaussianNameReciprocal.name_fast K a z hk ha
  have hp : Γ ⊢[PRAAx] pointCN P v := GaussianNamedDifference.name_regular F G x y h.andE₁ h.andE₂.andE₁
  have group := multiply_associative K J P z u v hk hj hp
  have unit := cross_trans _ _ _ _ _ _ (GaussianNameReciprocal.product_one K a z hk ha)
    (GaussianBoundedInverseApartness.ones_equivalent z v)
  have reduce := multiply_equivalent (multiplyF K J) oneF P P (multiplyData K J z u) v v v
    (multiply_fast K J z u hk hj) (one_fast v) hp hp (cross_to_diagonal _ _ _ _ unit)
    (cross_to_diagonal _ _ _ _ (cross_refl P v hp))
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ group)
    (cross_trans _ _ _ _ _ _ reduce (multiply_one_left P v hp))

theorem right_product (F G K : PR 2) (x y z a : PTm n) (h : Γ ⊢[PRAAx] input F G K x y z a) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF (nameF F G K) K) (GaussianNamedDifference.nameF F G)
      (rightData F G K x y z a) (GaussianNamedDifference.data x y) :=
  cross_trans _ _ _ _ _ _
    (multiply_commutative (nameF F G K) K (data F G K x y z a) z (name_regular F G K x y z a h) h.andE₂.andE₂.andE₁)
    (left_product F G K x y z a h)

theorem inverse_sample_bound (K : PR 2) (a z p : PTm n) (h : Γ ⊢[PRAAx] GaussianNameReciprocal.input K a z) : Γ ⊢[PRAAx]
    bounded (ap2 (GaussianNameReciprocal.nameF K) p (GaussianNameReciprocal.nameData a z)) (GaussianNameReciprocal.R a) one := by
  let t := GaussianFastValueCut.exponent (GaussianNameReciprocal.modulus a) p
  have fixed : Γ ⊢[PRAAx] ap2 (GaussianNameReciprocal.nameF K) p (GaussianNameReciprocal.nameData a z) ≐
      GaussianNameReciprocal.raw K a z t :=
    (GaussianNameReciprocal.name_at K a z p).eqTrans
      (GaussianNamedSmallPerturbationTransport.recode_fixed _ (GaussianRationalReciprocal.reciprocal_canonical _))
  exact GaussianRationalReciprocal.bound_congr fixed.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianNameReciprocal.raw_bound K a z t h.andE₁ h.andE₂)

theorem late_native_separated (K : PR 2) (a z t : PTm n) (h : Γ ⊢[PRAAx] GaussianNameReciprocal.input K a z) : Γ ⊢[PRAAx]
    GaussianNamedDifferenceQuotient.separated (nativeNumerator K a z t) (nativeDenominator K a z t) :=
  .andI (raw_den_positive _) (GaussianNameReciprocal.lower_norm_positive _ _ (GaussianNameReciprocal.R_positive a)
    (GaussianNameReciprocal.tail_lower K a z t h.andE₁ h.andE₂))

theorem late_native_value (K : PR 2) (a z t : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ofGaussian (nativeNumerator K a z t) (nativeDenominator K a z t))
      (ap2 K (t+GaussianNameReciprocal.anchor a) z) ConciseIPRA.PTm.zero one :=
  GaussianFastValueCut.recode_distance (GaussianNameReciprocal.tail K a z t)

theorem actual_named_increment_divided_difference_closed (F G K : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input F G K (var 0) (var 1) (var 2) (var 3) ⟶
      (pointCN (nameF F G K) (data F G K (var 0) (var 1) (var 2) (var 3)) ⋏
      (crossEquivalent (multiplyF K (nameF F G K)) (GaussianNamedDifference.nameF F G)
        (leftData F G K (var 0) (var 1) (var 2) (var 3)) (GaussianNamedDifference.data (var 0) (var 1)) ⋏
       crossEquivalent (multiplyF (nameF F G K) K) (GaussianNamedDifference.nameF F G)
        (rightData F G K (var 0) (var 1) (var 2) (var 3)) (GaussianNamedDifference.data (var 0) (var 1))))) :=
  closeUniv 4 (.impI (.andI (name_regular F G K _ _ _ _ Prf.hyp0)
    (.andI (left_product F G K _ _ _ _ Prf.hyp0) (right_product F G K _ _ _ _ Prf.hyp0))))

theorem actual_named_increment_late_native_separation_closed (K : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianNameReciprocal.input K (var 0) (var 1) ⟶
      GaussianNamedDifferenceQuotient.separated (nativeNumerator K (var 0) (var 1) (var 2))
        (nativeDenominator K (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (late_native_separated K _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedIncrementDifferenceQuotient
