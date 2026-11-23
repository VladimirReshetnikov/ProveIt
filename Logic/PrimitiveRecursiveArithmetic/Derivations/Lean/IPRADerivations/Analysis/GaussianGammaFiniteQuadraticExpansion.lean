import IPRADerivations.Analysis.GaussianGammaPolynomialQuadratic
import IPRADerivations.Analysis.GaussianGammaUnitCoefficientMass
import IPRADerivations.Analysis.GaussianShrinkingPolynomialTail
import IPRADerivations.Analysis.GaussianRationalRoundedPower

/-!
# A genuine cubic finite expansion of the original Gamma polynomials

The original stored coefficients give zero, one and the actual sampled
Euler constant exactly. The original full coefficient mass and shrinking
disk tail retain the cubic input factor at arbitrary finite horizons.
An independently requested Euler-constant observation contributes only
its true quadratic input factor, with no sampler or coefficient premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFiniteQuadraticExpansion

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaFiniteCoefficientPolynomial (polynomial totalDegree polynomial_length)
open GaussianGammaUnitCoefficientMass (budget)
open GaussianRationalHorner (qadd qmul qzero qadd_canonical qmul_canonical canonical evaluate positive_product)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr)
open GaussianRationalReciprocal (power)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalPowerExpansion (partialSum prefix_succ prefix_zero)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianOffDominantTerms (term)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def gammaPoint (q : PTm n) : PTm n := ap2 GaussianGammaCanonicalExponent.gammaF q zero
def quadratic (q w : PTm n) : PTm n := qadd w (qmul (gammaPoint q) (power w two))
def numerator (q r R a b : PTm n) : PTm n :=
  budget R*pw a (num 3)*unit q*unit r+pw a two*b*(unit q+unit r)
def denominator (q r b : PTm n) : PTm n := pw b (num 3)*unit q*unit r

@[simp] theorem subst_gammaPoint {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (gammaPoint q) = gammaPoint (Syn.subst σ q) := by simp [gammaPoint]
@[simp] theorem subst_quadratic {m : ℕ} (σ : Fin n → PTm m) (q w : PTm n) :
    Syn.subst σ (quadratic q w) = quadratic (Syn.subst σ q) (Syn.subst σ w) := by simp [quadratic]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (q r R a b : PTm n) :
    Syn.subst σ (numerator q r R a b) = numerator (Syn.subst σ q) (Syn.subst σ r) (Syn.subst σ R) (Syn.subst σ a) (Syn.subst σ b) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (q r b : PTm n) :
    Syn.subst σ (denominator q r b) = denominator (Syn.subst σ q) (Syn.subst σ r) (Syn.subst σ b) := by simp [denominator]

theorem total_degree_two (R L K : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    le two (totalDegree R L K) := by
  have h := GaussianGammaExponentCoefficientPolynomial.original_cutoff_positive R hR
  have head : Γ ⊢[PRAAx] le two (succ (two*R)) := le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right one h)
  exact le_trans head (le_add_right _ _)

theorem first_three (q R L K w : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K)
    (hw : Γ ⊢[PRAAx] canonical w) : Γ ⊢[PRAAx]
    partialSum (polynomial q R L K) (totalDegree R L K) w (num 3) ≐ quadratic q w := by
  let C := polynomial q R L K
  let N := totalDegree R L K
  have hN := total_degree_two R L K hR
  have c0 : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.coefficient C N zero ≐ qzero :=
    (Foundations.SequenceComposition.entry_congr (.eqRefl _) (monus_zero N)).eqTrans
      (GaussianGammaPolynomialConstantLinear.whole_constant q R L K)
  have t0 : Γ ⊢[PRAAx] term C N w zero ≐ qzero :=
    (qmul_congr c0 (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _)
  have p1 := (prefix_succ C N w zero (zero_le N)).eqTrans
    ((qadd_congr (prefix_zero C N w) t0).eqTrans (GaussianRationalSyntheticDivision.qzero_add qzero GaussianRationalSyntheticDivision.qzero_canonical))
  have t1 : Γ ⊢[PRAAx] term C N w one ≐ w :=
    (qmul_congr (GaussianGammaPolynomialConstantLinear.whole_linear q R L K hK) (GaussianRationalPowerAlgebra.power_one w hw)).eqTrans
      (GaussianPolynomialDeterminantTerms.one_mul_canonical w hw)
  have p2 := (prefix_succ C N w one (le_trans (le_succ_self one) hN)).eqTrans
    ((qadd_congr p1 t1).eqTrans (GaussianRationalSyntheticDivision.qzero_add w hw))
  have t2 : Γ ⊢[PRAAx] term C N w two ≐ qmul (gammaPoint q) (power w two) :=
    qmul_congr ((GaussianGammaPolynomialQuadratic.whole_quadratic q R L K hR hK).eqTrans
      (GaussianGammaCanonicalExponent.gamma_sample_at q).eqSymm) (.eqRefl _)
  have final := (prefix_succ C N w two hN).eqTrans (qadd_congr p2 t2)
  simpa only [quadratic,show (num 3 : PTm n) = succ two from rfl] using final

theorem original_cubic_error (q R L K w a b : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K)
    (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le a b) (hc : Γ ⊢[PRAAx] canonical w)
    (hw : Γ ⊢[PRAAx] bounded w a b) : Γ ⊢[PRAAx]
    distanceBounded (evaluate (polynomial q R L K) w) (quadratic q w) (budget R*pw a (num 3)) (pw b (num 3)) := by
  have raw := GaussianShrinkingPolynomialTail.finite_coefficient_tail (polynomial q R L K) (totalDegree R L K) two w
    (budget R) one a b (polynomial_length q R L K) (total_degree_two R L K hR) (le_refl one) hb hab
    (GaussianGammaUnitCoefficientMass.original_coefficient_mass q R L K hR) hw
  exact distance_congr (.eqRefl _) (first_three q R L K w hR hK hc) (.eqRefl _) (one_mul _) raw

theorem quadratic_coefficient_error (q r w a b : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hw : Γ ⊢[PRAAx] bounded w a b) : Γ ⊢[PRAAx]
    distanceBounded (quadratic q w) (quadratic r w) (pw a two*(unit q+unit r)) (pw b two*(unit q*unit r)) := by
  have hd := positive_product _ _ (unit_positive (Γ := Γ) q) (unit_positive r)
  have hp := GaussianFactorBudget.power_positive b two hb
  have hD := positive_product _ _ hp hd
  have raw := GaussianRationalReciprocal.bounded_product (power w two) (qsub (gammaPoint q) (gammaPoint r))
    (pw a two) (pw b two) (unit q+unit r) (unit q*unit r) hp hd
    (GaussianRationalReciprocal.bounded_power w a b two hb hw)
    (GaussianNameEquivalence.point_at GaussianGammaCanonicalExponent.gammaF zero q r GaussianGammaCanonicalExponent.gamma_regular)
  have products := GaussianRationalReciprocal.bound_congr (GaussianRationalRoundedPower.multiplication_difference _ _ _).eqSymm (.eqRefl _) (.eqRefl _) raw
  have swapped := distance_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (GaussianRationalPowerAlgebra.qmul_commutative _ _) (.eqRefl _) (.eqRefl _) products
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hD (GaussianRationalPowerDifference.distance_refl_zero w _ hD) swapped)

theorem original_independent_coefficient_error (q r R L K w a b : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K) (hb : Γ ⊢[PRAAx] le one b)
    (hab : Γ ⊢[PRAAx] le a b) (hc : Γ ⊢[PRAAx] canonical w) (hw : Γ ⊢[PRAAx] bounded w a b) : Γ ⊢[PRAAx]
    distanceBounded (evaluate (polynomial q R L K) w) (quadratic r w) (numerator q r R a b) (denominator q r b) := by
  have hcubic := original_cubic_error q R L K w a b hR hK hb hab hc hw
  have hquad := quadratic_coefficient_error q r w a b hb hw
  have hd := positive_product _ _ (unit_positive (Γ := Γ) q) (unit_positive r)
  have hp2 := GaussianFactorBudget.power_positive b two hb
  have hp3 := GaussianFactorBudget.power_positive b (num 3) hb
  have cube : Γ ⊢[PRAAx] pw b (num 3) ≐ pw b two*b := by
    simpa only [show (num 3 : PTm n) = succ two from rfl] using pw_succ (Γ := Γ) b two
  have hD : Γ ⊢[PRAAx] le one (denominator q r b) := positive_product _ _ (positive_product _ _ hp3 (unit_positive q)) (unit_positive r)
  have first := distance_radius_mono _ _ _ _ (budget R*pw a (num 3)*unit q*unit r) (denominator q r b) hp3 hD
    (le_of_eq_add (d := zero) (by unfold denominator; ipra_ring)) hcubic
  have last := distance_radius_mono _ _ _ _ (pw a two*b*(unit q+unit r)) (denominator q r b) (positive_product _ _ hp2 hd) hD
    (le_of_eq_add (d := zero) (by
      unfold denominator
      apply deriveNat
      have e := natEq cube
      ipra_simps
      rw [e]
      ring)) hquad
  exact distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ hD first last)

theorem actual_original_Gamma_finite_cubic_expansion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((le one (var 1) ⋏ (le one (var 3) ⋏ (le one (var 6) ⋏ (le (var 5) (var 6) ⋏
      (canonical (var 4) ⋏ bounded (var 4) (var 5) (var 6)))))) ⟶
      distanceBounded (evaluate (polynomial (var 0) (var 1) (var 2) (var 3)) (var 4)) (quadratic (var 0) (var 4))
        (budget (var 1)*pw (var 5) (num 3)) (pw (var 6) (num 3))) :=
  closeUniv 7 (.impI (original_cubic_error _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂))

theorem actual_original_Gamma_finite_independent_quadratic_expansion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((le one (var 2) ⋏ (le one (var 4) ⋏ (le one (var 7) ⋏ (le (var 6) (var 7) ⋏
      (canonical (var 5) ⋏ bounded (var 5) (var 6) (var 7)))))) ⟶
      distanceBounded (evaluate (polynomial (var 0) (var 2) (var 3) (var 4)) (var 5)) (quadratic (var 1) (var 5))
        (numerator (var 0) (var 1) (var 2) (var 6) (var 7)) (denominator (var 0) (var 1) (var 7))) :=
  closeUniv 8 (.impI (original_independent_coefficient_error _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaFiniteQuadraticExpansion
