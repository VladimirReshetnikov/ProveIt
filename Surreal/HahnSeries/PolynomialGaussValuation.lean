import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Finset.Lattice.Fold
import Surreal.HahnSeries.StandardPart

/-!
# Weighted Gauss valuation of Hahn-coefficient polynomials

This constructs the valuation in `polynomial:eq:weighted` and proves the
valuation identities of `polynomial:lem:gaussvaluation` for an arbitrary
set-sized ordered abelian exponent group.

Regrouping a polynomial as a Hahn series with coefficients in `K[X]`
separates polynomial degrees: its coefficient of `X^j t^g` is the
coefficient of `t^(g-jρ)` in the original `j`th coefficient. The ordinary
Hahn valuation therefore gives the weighted minimum without cancellation
between different polynomial degrees. Translation supplies the center.
No real-valued norm, Archimedean assumption, algebraic closedness, or surreal
normal-form identification is used.

The initial polynomial is the leading coefficient in this regrouped Hahn
series. Its normalization formula is proved coefficientwise using the
existing standard-part map, including nonnegativity of every normalized
coefficient and nonvanishing for a nonzero polynomial. The active indices
are exactly its support, whose extrema are its trailing and leading degrees.
Initial-polynomial root counts are separate assertions.
-/

namespace Surreal.HahnSeries

open Polynomial
open scoped _root_.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K]

/-- Regard each Hahn coefficient as a constant polynomial. -/
def mapCoeffsToPolynomial : K⟦Γ⟧ →+* K[X]⟦Γ⟧ where
  toFun x := x.map (Polynomial.C : K →+* K[X])
  map_zero' := _root_.HahnSeries.map_zero (Polynomial.C : K →+* K[X]).toZeroHom
  map_one' := _root_.HahnSeries.map_one (Polynomial.C : K →+* K[X]).toMonoidWithZeroHom
  map_add' _ _ := _root_.HahnSeries.map_add (Polynomial.C : K →+* K[X]).toAddMonoidHom
  map_mul' _ _ := _root_.HahnSeries.map_mul (Polynomial.C : K →+* K[X]).toNonUnitalRingHom

@[simp] theorem coeff_mapCoeffsToPolynomial (x : K⟦Γ⟧) (g : Γ) :
    (mapCoeffsToPolynomial x).coeff g = C (x.coeff g) := rfl

/-- Embedding coefficients as constants preserves Hahn order, including zero. -/
@[simp] theorem orderTop_mapCoeffsToPolynomial (x : K⟦Γ⟧) :
    (mapCoeffsToPolynomial x).orderTop = x.orderTop := by
  apply le_antisymm
  · apply _root_.HahnSeries.le_orderTop_iff_forall.mpr
    intro g hg
    have h := _root_.HahnSeries.coeff_eq_zero_of_lt_orderTop hg
    exact Polynomial.C_eq_zero.mp h
  · apply _root_.HahnSeries.le_orderTop_iff_forall.mpr
    intro g hg
    rw [coeff_mapCoeffsToPolynomial,
      _root_.HahnSeries.coeff_eq_zero_of_lt_orderTop hg, map_zero]

/-- Regroup polynomial and Hahn exponents after the substitution `X ↦ t^ρ X`.
Only a finite polynomial is substituted, so every exponent `ρ` is allowed. -/
def gaussExpansion (ρ : Γ) : K⟦Γ⟧[X] →+* K[X]⟦Γ⟧ :=
  Polynomial.eval₂RingHom mapCoeffsToPolynomial (_root_.HahnSeries.single ρ X)

/-- The coefficient formula preventing cancellation between distinct
polynomial degrees in `polynomial:eq:weighted`. -/
theorem coeff_coeff_gaussExpansion (ρ : Γ) (P : K⟦Γ⟧[X]) (g : Γ) (j : ℕ) :
    ((gaussExpansion ρ P).coeff g).coeff j = (P.coeff j).coeff (g - j • ρ) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, _root_.HahnSeries.coeff_add, Polynomial.coeff_add, hP, hQ]
  | monomial n c =>
    change (((monomial n c).eval₂ mapCoeffsToPolynomial
      (_root_.HahnSeries.single ρ X)).coeff g).coeff j = _
    rw [eval₂_monomial, _root_.HahnSeries.single_pow,
      _root_.HahnSeries.coeff_mul_single, coeff_mapCoeffsToPolynomial,
      Polynomial.coeff_C_mul_X_pow]
    by_cases h : j = n <;> simp [h, Polynomial.coeff_monomial, eq_comm]

/-- Regrouping is injective, even at negative or zero weight. -/
theorem gaussExpansion_injective (ρ : Γ) :
    Function.Injective (gaussExpansion (K := K) ρ) := by
  intro P Q h
  apply Polynomial.ext
  intro j
  apply _root_.HahnSeries.ext
  funext g
  have hc := congrArg (fun H : K[X]⟦Γ⟧ => (H.coeff (g + j • ρ)).coeff j) h
  simpa only [coeff_coeff_gaussExpansion, add_sub_cancel_right] using hc

/-- A single polynomial monomial has its coefficient valuation shifted by
its weighted polynomial degree. -/
theorem orderTop_gaussExpansion_monomial (ρ : Γ) (j : ℕ) (c : K⟦Γ⟧) :
    (gaussExpansion ρ (monomial j c)).orderTop = c.orderTop + (j • ρ : Γ) := by
  change ((monomial j c).eval₂ mapCoeffsToPolynomial
    (_root_.HahnSeries.single ρ X)).orderTop = _
  rw [eval₂_monomial, _root_.HahnSeries.single_pow, _root_.HahnSeries.orderTop_mul,
    orderTop_mapCoeffsToPolynomial,
    _root_.HahnSeries.orderTop_single (pow_ne_zero _ Polynomial.X_ne_zero)]

/-- The regrouped Hahn order is exactly the finite weighted coefficient
minimum in `polynomial:eq:weighted`. Empty support gives `⊤`. -/
theorem orderTop_gaussExpansion_eq_inf (ρ : Γ) (P : K⟦Γ⟧[X]) :
    (gaussExpansion ρ P).orderTop =
      P.support.inf (fun j => (P.coeff j).orderTop + (j • ρ : Γ)) := by
  classical
  apply le_antisymm
  · apply Finset.le_inf
    intro j hj
    have hj0 : P.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    have hc : (P.coeff j).coeff (P.coeff j).order ≠ 0 :=
      _root_.HahnSeries.coeff_order_eq_zero.not.mpr hj0
    have hg : (gaussExpansion ρ P).coeff ((P.coeff j).order + j • ρ) ≠ 0 := by
      intro hzero
      have h := congrArg (fun q : K[X] => q.coeff j) hzero
      rw [coeff_coeff_gaussExpansion, add_sub_cancel_right] at h
      exact hc h
    have hle := _root_.HahnSeries.orderTop_le_of_coeff_ne_zero hg
    simpa only [WithTop.coe_add,
      _root_.HahnSeries.order_eq_orderTop_of_ne_zero hj0] using hle
  · have hsum : gaussExpansion ρ P =
        ∑ j ∈ P.support, gaussExpansion ρ (monomial j (P.coeff j)) := by
      have h := congrArg (gaussExpansion (K := K) ρ) P.sum_monomial_eq
      simpa only [Polynomial.sum, map_sum] using h.symm
    rw [hsum]
    apply (_root_.HahnSeries.addVal Γ K[X]).map_le_sum
    intro j hj
    change _ ≤ (gaussExpansion ρ (monomial j (P.coeff j))).orderTop
    rw [orderTop_gaussExpansion_monomial]
    exact Finset.inf_le hj

/-- Regroup after the centered substitution `P(a + t^ρ X)`. -/
def centeredGaussExpansion (a : K⟦Γ⟧) (ρ : Γ) : K⟦Γ⟧[X] →+* K[X]⟦Γ⟧ :=
  (gaussExpansion ρ).comp (taylorEquiv a).toRingEquiv.toRingHom

@[simp] theorem centeredGaussExpansion_apply (a : K⟦Γ⟧) (ρ : Γ) (P : K⟦Γ⟧[X]) :
    centeredGaussExpansion a ρ P = gaussExpansion ρ (taylor a P) := rfl

theorem centeredGaussExpansion_injective (a : K⟦Γ⟧) (ρ : Γ) :
    Function.Injective (centeredGaussExpansion a ρ) :=
  (gaussExpansion_injective ρ).comp (taylorEquiv a).injective

/-- The weighted Gauss valuation `w_(a,ρ)` in `polynomial:eq:weighted`,
as a native additive valuation with values in the arbitrary exponent group. -/
def weightedGaussVal (a : K⟦Γ⟧) (ρ : Γ) : AddValuation K⟦Γ⟧[X] (WithTop Γ) :=
  (_root_.HahnSeries.addVal Γ K[X]).comap (centeredGaussExpansion a ρ)

@[simp] theorem weightedGaussVal_apply (a : K⟦Γ⟧) (ρ : Γ) (P : K⟦Γ⟧[X]) :
    weightedGaussVal a ρ P = (centeredGaussExpansion a ρ P).orderTop := rfl

/-- The centered Taylor-coefficient minimum in `polynomial:eq:weighted`. -/
theorem weightedGaussVal_eq_inf (a : K⟦Γ⟧) (ρ : Γ) (P : K⟦Γ⟧[X]) :
    weightedGaussVal a ρ P = (taylor a P).support.inf
      (fun j => ((taylor a P).coeff j).orderTop + (j • ρ : Γ)) :=
  orderTop_gaussExpansion_eq_inf ρ (taylor a P)

/-- Infinity occurs precisely for the zero polynomial. -/
@[simp] theorem weightedGaussVal_eq_top_iff (a : K⟦Γ⟧) (ρ : Γ) (P : K⟦Γ⟧[X]) :
    weightedGaussVal a ρ P = ⊤ ↔ P = 0 := by
  rw [weightedGaussVal_apply, _root_.HahnSeries.orderTop_eq_top]
  exact map_eq_zero_iff _ (centeredGaussExpansion_injective a ρ)

/-- Multiplicativity in `polynomial:lem:gaussvaluation`, including zero. -/
theorem weightedGaussVal_mul (a : K⟦Γ⟧) (ρ : Γ) (P Q : K⟦Γ⟧[X]) :
    weightedGaussVal a ρ (P * Q) = weightedGaussVal a ρ P + weightedGaussVal a ρ Q :=
  (weightedGaussVal a ρ).map_mul P Q

/-- The ultrametric inequality in `polynomial:lem:gaussvaluation`. -/
theorem weightedGaussVal_add (a : K⟦Γ⟧) (ρ : Γ) (P Q : K⟦Γ⟧[X]) :
    min (weightedGaussVal a ρ P) (weightedGaussVal a ρ Q) ≤ weightedGaussVal a ρ (P + Q) :=
  (weightedGaussVal a ρ).map_add P Q

/-- The initial polynomial in `polynomial:eq:weighted`, in the regrouped
Hahn presentation. Its coefficientwise standard-part formula is proved
below; for zero it is defined to be zero. -/
def gaussInitial (a : K⟦Γ⟧) (ρ : Γ) (P : K⟦Γ⟧[X]) : K[X] :=
  (centeredGaussExpansion a ρ P).leadingCoeff

/-- The initial polynomial of a nonzero polynomial is nonzero. -/
theorem gaussInitial_ne_zero (a : K⟦Γ⟧) (ρ : Γ) (P : K⟦Γ⟧[X]) (hP : P ≠ 0) :
    gaussInitial a ρ P ≠ 0 := by
  apply _root_.HahnSeries.leadingCoeff_ne_zero.mpr
  exact (map_eq_zero_iff _ (centeredGaussExpansion_injective a ρ)).not.mpr hP

/-- Multiplicativity of initial polynomials in
`polynomial:lem:gaussvaluation`, with the zero case included. -/
theorem gaussInitial_mul (a : K⟦Γ⟧) (ρ : Γ) (P Q : K⟦Γ⟧[X]) :
    gaussInitial a ρ (P * Q) = gaussInitial a ρ P * gaussInitial a ρ Q := by
  simp only [gaussInitial, map_mul, _root_.HahnSeries.leadingCoeff_mul]

/-- Initial coefficients select the Taylor coefficient at its weighted
leading exponent. For nonzero `P`, the chosen exponent is its Gauss value. -/
theorem coeff_gaussInitial (a : K⟦Γ⟧) (ρ : Γ) (P : K⟦Γ⟧[X]) (j : ℕ) :
    (gaussInitial a ρ P).coeff j = ((taylor a P).coeff j).coeff
      ((centeredGaussExpansion a ρ P).order - j • ρ) := by
  rw [gaussInitial, _root_.HahnSeries.leadingCoeff_eq]
  exact coeff_coeff_gaussExpansion ρ (taylor a P) _ j

/-- The `j`th coefficient after multiplying `P(a + t^ρ X)` by `t^(-λ)`,
where `λ` is the finite Gauss value of nonzero `P`. The zero polynomial
uses the native zero-series `order` convention and gives zero coefficients. -/
def normalizedGaussCoefficient (a : K⟦Γ⟧) (ρ : Γ) (P : K⟦Γ⟧[X]) (j : ℕ) : K⟦Γ⟧ :=
  _root_.HahnSeries.single (-(centeredGaussExpansion a ρ P).order) 1 *
    ((taylor a P).coeff j * _root_.HahnSeries.single (j • ρ) 1)

/-- Every normalized coefficient in `polynomial:eq:weighted` has
nonnegative order; the Gauss minimum is the common lower bound. -/
theorem orderTop_normalizedGaussCoefficient_nonneg (a : K⟦Γ⟧) (ρ : Γ)
    (P : K⟦Γ⟧[X]) (hP : P ≠ 0) (j : ℕ) :
    0 ≤ (normalizedGaussCoefficient a ρ P j).orderTop := by
  have hE : centeredGaussExpansion a ρ P ≠ 0 :=
    (map_eq_zero_iff _ (centeredGaussExpansion_injective a ρ)).not.mpr hP
  have hbound : ((centeredGaussExpansion a ρ P).order : WithTop Γ) ≤
      ((taylor a P).coeff j).orderTop + (j • ρ : Γ) := by
    rw [_root_.HahnSeries.order_eq_orderTop_of_ne_zero hE,
      ← weightedGaussVal_apply, weightedGaussVal_eq_inf]
    by_cases hj : (taylor a P).coeff j = 0
    · simp [hj]
    · exact Finset.inf_le (Polynomial.mem_support_iff.mpr hj)
  rw [normalizedGaussCoefficient, _root_.HahnSeries.orderTop_mul,
    _root_.HahnSeries.orderTop_mul, _root_.HahnSeries.orderTop_single one_ne_zero,
    _root_.HahnSeries.orderTop_single one_ne_zero]
  calc
    0 = ((-(centeredGaussExpansion a ρ P).order : Γ) : WithTop Γ) +
        ((centeredGaussExpansion a ρ P).order : WithTop Γ) := by
      rw [← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero]
    _ ≤ _ := add_le_add le_rfl hbound

/-- Extracting the normalized coefficient at exponent zero gives the
corresponding initial-polynomial coefficient in `polynomial:eq:weighted`. -/
theorem coeff_gaussInitial_eq_normalized_coeff_zero (a : K⟦Γ⟧) (ρ : Γ)
    (P : K⟦Γ⟧[X]) (j : ℕ) :
    (gaussInitial a ρ P).coeff j = (normalizedGaussCoefficient a ρ P j).coeff 0 := by
  rw [coeff_gaussInitial, normalizedGaussCoefficient,
    _root_.HahnSeries.coeff_single_mul, _root_.HahnSeries.coeff_mul_single]
  simp only [zero_sub, neg_neg, one_mul, mul_one]

/-- The coefficientwise standard-part definition of the initial
polynomial in `polynomial:eq:weighted`. -/
theorem coeff_gaussInitial_eq_standardPart (a : K⟦Γ⟧) (ρ : Γ)
    (P : K⟦Γ⟧[X]) (hP : P ≠ 0) (j : ℕ) :
    (gaussInitial a ρ P).coeff j = standardPart Γ K
      ⟨normalizedGaussCoefficient a ρ P j,
        (mem_nonnegativeSubring _).mpr
          (orderTop_normalizedGaussCoefficient_nonneg a ρ P hP j)⟩ :=
  coeff_gaussInitial_eq_normalized_coeff_zero a ρ P j

/-- At least one normalized coefficient has valuation zero, as asserted
immediately after `polynomial:eq:weighted`. -/
theorem exists_normalizedGaussCoefficient_orderTop_eq_zero (a : K⟦Γ⟧) (ρ : Γ)
    (P : K⟦Γ⟧[X]) (hP : P ≠ 0) :
    ∃ j, (normalizedGaussCoefficient a ρ P j).orderTop = 0 := by
  refine ⟨(gaussInitial a ρ P).natDegree,
    le_antisymm ?_ (orderTop_normalizedGaussCoefficient_nonneg a ρ P hP _)⟩
  apply _root_.HahnSeries.orderTop_le_of_coeff_ne_zero
  rw [← coeff_gaussInitial_eq_normalized_coeff_zero, Polynomial.coeff_natDegree]
  exact Polynomial.leadingCoeff_ne_zero.mpr (gaussInitial_ne_zero a ρ P hP)

/-- The active-index criterion in `polynomial:eq:active`: exactly the
Taylor coefficients attaining the weighted minimum survive normalization. -/
theorem coeff_gaussInitial_ne_zero_iff (a : K⟦Γ⟧) (ρ : Γ)
    (P : K⟦Γ⟧[X]) (hP : P ≠ 0) (j : ℕ) :
    (gaussInitial a ρ P).coeff j ≠ 0 ↔
      ((taylor a P).coeff j).orderTop + (j • ρ : Γ) = weightedGaussVal a ρ P := by
  have hE : centeredGaussExpansion a ρ P ≠ 0 :=
    (map_eq_zero_iff _ (centeredGaussExpansion_injective a ρ)).not.mpr hP
  have hcoeff : (normalizedGaussCoefficient a ρ P j).coeff 0 ≠ 0 ↔
      (normalizedGaussCoefficient a ρ P j).orderTop = 0 := by
    constructor
    · intro hc
      exact le_antisymm (_root_.HahnSeries.orderTop_le_of_coeff_ne_zero hc)
        (orderTop_normalizedGaussCoefficient_nonneg a ρ P hP j)
    · exact _root_.HahnSeries.coeff_orderTop_ne
  rw [coeff_gaussInitial_eq_normalized_coeff_zero, hcoeff,
    normalizedGaussCoefficient, _root_.HahnSeries.orderTop_mul,
    _root_.HahnSeries.orderTop_mul, _root_.HahnSeries.orderTop_single one_ne_zero,
    _root_.HahnSeries.orderTop_single one_ne_zero, weightedGaussVal_apply,
    ← _root_.HahnSeries.order_eq_orderTop_of_ne_zero hE]
  have hz : ((-(centeredGaussExpansion a ρ P).order : Γ) : WithTop Γ) +
      ((centeredGaussExpansion a ρ P).order : WithTop Γ) = 0 := by
    rw [← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero]
  rw [← hz]
  exact WithTop.add_left_inj WithTop.coe_ne_top

/-- The active indices of `polynomial:eq:active` form precisely the
finite support of the initial polynomial. -/
theorem support_gaussInitial_eq_active (a : K⟦Γ⟧) (ρ : Γ)
    (P : K⟦Γ⟧[X]) (hP : P ≠ 0) :
    (↑(gaussInitial a ρ P).support : Set ℕ) =
      {j | ((taylor a P).coeff j).orderTop + (j • ρ : Γ) = weightedGaussVal a ρ P} := by
  ext j
  simp only [Finset.mem_coe, Polynomial.mem_support_iff, Set.mem_setOf_eq,
    coeff_gaussInitial_ne_zero_iff a ρ P hP]

/-- The initial polynomial's trailing degree and degree are respectively
the least and greatest active indices, as stated after `polynomial:eq:active`.
Nonvanishing makes both natural-degree conventions valid. -/
theorem gaussInitial_active_extrema (a : K⟦Γ⟧) (ρ : Γ)
    (P : K⟦Γ⟧[X]) (hP : P ≠ 0) :
    IsLeast {j | ((taylor a P).coeff j).orderTop + (j • ρ : Γ) = weightedGaussVal a ρ P}
        (gaussInitial a ρ P).natTrailingDegree ∧
      IsGreatest {j | ((taylor a P).coeff j).orderTop + (j • ρ : Γ) = weightedGaussVal a ρ P}
        (gaussInitial a ρ P).natDegree := by
  have hI := gaussInitial_ne_zero a ρ P hP
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (coeff_gaussInitial_ne_zero_iff a ρ P hP _).mp
      (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hI)
  · intro j hj
    exact Polynomial.natTrailingDegree_le_of_ne_zero
      ((coeff_gaussInitial_ne_zero_iff a ρ P hP j).mpr hj)
  · apply (coeff_gaussInitial_ne_zero_iff a ρ P hP _).mp
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hI
  · intro j hj
    exact Polynomial.le_natDegree_of_ne_zero
      ((coeff_gaussInitial_ne_zero_iff a ρ P hP j).mpr hj)

end
end Surreal.HahnSeries
