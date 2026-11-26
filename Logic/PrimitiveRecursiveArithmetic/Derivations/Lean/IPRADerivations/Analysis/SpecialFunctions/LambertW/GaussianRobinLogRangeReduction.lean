import IPRADerivations.Analysis.Exponential.GaussianRobinOddExponential
import IPRADerivations.Analysis.Gamma.GammaMeshRobinLogBridge

/-!
# Exponentials of the original range-reduced logarithm components

The binary range reduction stores a fixed odd series at 1/3 and a reduced
one at the actual fraction dt/st. Their exponentials are the exact rational
constants 2 and a/Bt at independent observation precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRobinLogRangeReduction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval (Bt dt st c3 a_eq one_le_Bt z_third)
open GaussianRobinOddLogarithmName (source inputs)
open GaussianRobinLogarithmParity (native)
open GaussianRobinOddExponential (constantF oddF ratio)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianRationalHorner
  (ofGaussian ofGaussian_represents ofGaussian_canonical canonical_unique represents_congr positive_product)
open GaussianRationalSyntheticDivision (rescale_to)
open ComplexLogarithmRemainder (scale)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def quotient (a b : PTm n) : PTm n := ofGaussian (native a) b

theorem reduced_source (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) (ha : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] source (dt a b) (st a b) := by
  have hp := le_trans (le_trans hb ha) (le_add_right a (Bt a b))
  have bound : Γ ⊢[PRAAx] le (c3*dt a b) (st a b) :=
    le_congr (mul_comm _ _) (one_mul _) (z_third hb ha)
  exact .andI hp (le_trans (le_of_eq_add (d := dt a b) (by ipra_ring)) bound)

private theorem double_fraction (p q a b : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hp : Γ ⊢[PRAAx] p ≐ two*a) (hq : Γ ⊢[PRAAx] q ≐ b*two) :
    Γ ⊢[PRAAx] quotient p q ≐ quotient a b := by
  have ht := le_succ_self (Γ := Γ) one
  have hbd := positive_product _ _ hb ht
  have hq1 := le_congr (.eqRefl _) hq.eqSymm hbd
  have old := ofGaussian_represents (native p) q hq1
  have scaled := rescale_to (quotient a b) (native a) b two (b*two)
    (ofGaussian_represents _ _ hb) (.eqRefl _)
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (native p) (scale two (native a)) := by
    have ep := natEq hp
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [native,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
        GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,ep] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ _ (ofGaussian_canonical _ _ hq1) (ofGaussian_canonical _ _ hb) hbd
    (represents_congr (.eqRefl _) e hq old) scaled

theorem reduced_ratio (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) (ha : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] ratio (dt a b) (st a b) ≐ quotient a (Bt a b) := by
  have e := natEq (a_eq hb ha)
  have hsum : Γ ⊢[PRAAx] st a b+dt a b ≐ two*a := by
    unfold st
    apply deriveNat
    ipra_simps
    rw [e]
    ring
  have he : Γ ⊢[PRAAx] st a b ≐ Bt a b*two+dt a b := by
    unfold st
    apply deriveNat
    ipra_simps
    rw [e]
    ring
  have hdiff := (congrMonus he (.eqRefl _)).eqTrans (add_monus _ _)
  exact double_fraction _ _ _ _ (one_le_Bt hb) hsum hdiff

theorem base_ratio : Γ ⊢[PRAAx] ratio one c3 ≐ quotient two one := by
  have e : Γ ⊢[PRAAx] (c3 : PTm n) ≐ two+one := by ipra_ring
  have d := (congrMonus e (.eqRefl one)).eqTrans (add_monus two one)
  exact double_fraction _ _ _ _ (le_refl one) (by ipra_ring)
    (d.eqTrans (one_mul _).eqSymm)

theorem original_binary_component (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) (ha : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianRadiusExponentialName.nameF oddF) constantF
      (GaussianRadiusExponentialName.data (num 3) (inputs (dt a b) (st a b))) (quotient a (Bt a b)) :=
  cross_trans _ _ _ _ _ _
    (GaussianRobinOddExponential.odd_exponential_ratio _ _ (reduced_source a b hb ha))
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (reduced_ratio a b hb ha))

theorem original_base_component : Γ ⊢[PRAAx] crossEquivalent (GaussianRadiusExponentialName.nameF oddF) constantF
    (GaussianRadiusExponentialName.data (num 3) (inputs one c3)) (quotient two one) := by
  have h : Γ ⊢[PRAAx] source one c3 := .andI
    (le_of_eq_add (d := two) (by ipra_ring)) (le_of_eq_add (d := one) (by ipra_ring))
  exact cross_trans _ _ _ _ _ _
    (GaussianRobinOddExponential.odd_exponential_ratio _ _ h)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ base_ratio)

theorem original_Robin_binary_component_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ le (var 1) (var 0) ⟶
      crossEquivalent (GaussianRadiusExponentialName.nameF oddF) constantF
        (GaussianRadiusExponentialName.data (num 3) (inputs (dt (var 0) (var 1)) (st (var 0) (var 1))))
        (quotient (var 0) (Bt (var 0) (var 1)))) :=
  closeUniv 2 (.impI (.impI (original_binary_component _ _ Prf.hyp1 Prf.hyp0)))

theorem original_Robin_base_component_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    crossEquivalent (GaussianRadiusExponentialName.nameF oddF) constantF
      (GaussianRadiusExponentialName.data (num 3) (inputs one c3)) (quotient two one) :=
  original_base_component

end LeanProofs.IPRA.Analysis.GaussianRobinLogRangeReduction
