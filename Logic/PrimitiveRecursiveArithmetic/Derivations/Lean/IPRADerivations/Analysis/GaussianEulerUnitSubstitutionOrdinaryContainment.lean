import IPRADerivations.Analysis.GaussianEulerUnitSubstitutionOrdinaryEndpoints
import IPRADerivations.Analysis.RationalNativeFractionDisplacement

/-!
# Cofinal containment of every proper rational unit panel

If the stage unit is at least the denominator of a certified interior
rational panel, the actual rounded ordinary panel contains it. The
comparison is expressed in native cross products for exact splitting
after rescaling to a common denominator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionOrdinaryContainment

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitSubstitutionOrdinaryImproper (source resolution)
open GaussianEulerUnitSubstitutionOrdinaryEndpoints
  (denominator leftNumerator rightNumerator endpointBounds later_endpoints)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (qzero ofGaussian_represents scalar_congr)
open GaussianRationalSyntheticDivision (qone)
open ComplexLogarithmRemainder (zeroCode oneCode)
open GaussianRootAlgebra (re_zero re_one)
open RationalNativeFractionDisplacement (native_upper)
open RationalValueBounds (radius upper_of_radius radius_symmetric)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private theorem real_zero : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (qzero : PTm n)) (ZT.ofNat zero) one :=
  scalar_congr (.eqRefl _) (ZT.derive (by rw [re_zero,ZT.toZ_ofNat]; ipra_simps)) (.eqRefl _)
    (ofGaussian_represents zeroCode one (le_refl _)).andE₁

private theorem real_one : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (qone : PTm n)) (ZT.ofNat one) one :=
  scalar_congr (.eqRefl _) (ZT.derive (by rw [re_one,ZT.toZ_ofNat]; ipra_simps; ring)) (.eqRefl _)
    (ofGaussian_represents oneCode one (le_refl _)).andE₁

def contains (x y M a C E : PTm n) : Fm PTm n :=
  le (E*x) (M*a) ⋏ le (M*(a+C)) (E*y)

theorem contains_of_radii (x y M a C E U : PTm n)
    (strict : Γ ⊢[PRAAx] lt y M)
    (hl : Γ ⊢[PRAAx] radius (fraction x M) (fstT qzero) one U)
    (hu : Γ ⊢[PRAAx] radius (fraction y M) (fstT qone) one U)
    (ha : Γ ⊢[PRAAx] le one a) (hr : Γ ⊢[PRAAx] lt (a+C) E) (hs : Γ ⊢[PRAAx] le E U) :
    Γ ⊢[PRAAx] contains x y M a C E := by
  let d := monus M y
  have hy : Γ ⊢[PRAAx] le y M := le_of_lt strict
  have hm : Γ ⊢[PRAAx] le one M := le_trans (zero_lt_succ y) strict
  have left := native_upper (fraction x M) (fstT qzero) x M zero one one U
    (fraction_represents x M hm) real_zero (upper_of_radius _ _ _ _ hl)
  have right := native_upper (fstT qone) (fraction y M) one one y M one U
    real_one (fraction_represents y M hm) (upper_of_radius _ _ _ _ (radius_symmetric _ _ _ _ hu))
  have leftBudget : Γ ⊢[PRAAx] le (U*x) M := le_congr (by ipra_ring) (by ipra_ring) left
  have rightBudget : Γ ⊢[PRAAx] le (U*M) (U*y+M) := le_congr (by ipra_ring) (by ipra_ring) right
  have split : Γ ⊢[PRAAx] M ≐ y+d := eq_add_of_le hy
  have splitEquation := natEq split
  simp only [Q.mk_add,map_add] at splitEquation
  have gap : Γ ⊢[PRAAx] le (U*d) M := by
    ipra_le sl rightBudget with -𝔞 U*splitEquation
  have scaled := le_trans (mul_le_mul_right d hs) gap
  have panelRight : Γ ⊢[PRAAx] le (a+C+one) E := le_congr (succ_eq_add_one _) (.eqRefl _) hr
  refine .andI (le_trans (mul_le_mul_right x hs) (le_trans leftBudget
    (le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right M ha)))) ?_
  show Γ ⊢[PRAAx] le (M*(a+C)) (E*y)
  ipra_le sl scaled+𝔞 M*sl panelRight with 𝔞 E*splitEquation

theorem contain_of_endpoint_bounds (p j A R a C E : PTm n)
    (h : Γ ⊢[PRAAx] endpointBounds p j A R) (ha : Γ ⊢[PRAAx] le one a)
    (hr : Γ ⊢[PRAAx] lt (a+C) E) (hs : Γ ⊢[PRAAx] le E (unit p)) : Γ ⊢[PRAAx]
    contains (leftNumerator p j A R) (rightNumerator p j A R) (denominator p j A R) a C E :=
  contains_of_radii _ _ _ a C E (unit p) h.andE₁.andE₂ h.andE₂.andE₁ h.andE₂.andE₂ ha hr hs

theorem original_panel_contains (p j z R B A a C E : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hj : Γ ⊢[PRAAx] le (resolution p) j) (ha : Γ ⊢[PRAAx] le one a)
    (hr : Γ ⊢[PRAAx] lt (a+C) E) (hs : Γ ⊢[PRAAx] le E (unit p)) : Γ ⊢[PRAAx]
    contains (leftNumerator p j A R) (rightNumerator p j A R) (denominator p j A R) a C E :=
  contain_of_endpoint_bounds p j A R a C E (later_endpoints p j z R B A h hj) ha hr hs

def containmentIndex (p E : PTm n) : PTm n := GaussianFastValueCut.exponent E p

theorem containment_index_later (p E : PTm n) : Γ ⊢[PRAAx] le p (containmentIndex p E) := le_add_right _ _

theorem containment_index_budget (p E : PTm n) : Γ ⊢[PRAAx] le E (unit (containmentIndex p E)) :=
  le_trans (le_congr (one_mul E) (mul_comm _ _) (mul_le_mul_right E (unit_positive p)))
    (GaussianFastValueCut.query_budget E p)

theorem actual_ordinary_unit_contains_proper_rational_panel_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((source (var 2) (var 3) (var 4) (var 5) ⋏ (le (resolution (var 0)) (var 1) ⋏
      (le one (var 6) ⋏ (lt (var 6+var 7) (var 8) ⋏ le (var 8) (unit (var 0)))))) ⟶
      contains (leftNumerator (var 0) (var 1) (var 5) (var 3)) (rightNumerator (var 0) (var 1) (var 5) (var 3))
        (denominator (var 0) (var 1) (var 5) (var 3)) (var 6) (var 7) (var 8)) :=
  closeUniv 9 (.impI (original_panel_contains _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionOrdinaryContainment
