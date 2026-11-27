import IPRADerivations.Analysis.Stirling.AllOrders.Bernoulli.GaussianStirlingAllOrderBernoulliEnvelope
import IPRADerivations.Analysis.Stirling.AllOrders.PairedPanels.GaussianStirlingAllOrderPairedWeight
import IPRADerivations.Analysis.Inequalities.NonnegativeArithmetic.RationalNonnegativePowerOrder
import IPRADerivations.Analysis.RationalArithmetic.Powers.RationalPowerBounds.RationalReciprocalPowerTail

/-!
# Literal periodic Bernoulli kernel on a panel grid

At row r of panel k, the positive reciprocal-power weight is
`(A/B + k + r/M)^(-(q+1))`. The row uses the actual centered
Bernoulli sample, and its reflected row gives the paired weight
used in the strict comparison.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderKernel

open_ipra
open GaussianStirlingAllOrderCenteredBernoulli (sample reflected_sample)
open GaussianStirlingAllOrderBernoulliEnvelope (cap sample_envelope subst_sample)
open GaussianStirlingAllOrderPairedWeight (weight pairWeight)
open GaussianEuclideanDistanceName (fraction fraction_represents fraction_order)
open GaussianRationalHorner (positive_product)
open GaussianFactorBudget (power_positive)
open GaussianRationalL1 (nonnegative_of_representation nonnegative_of_lower)
open RationalArithmetic (add multiply represents)
open RationalAlgebra (multiply_congr multiply_commutative multiply_add add_congr)
open RationalArgmin (rationalLE rationalLE_congr transitive)
open RationalSupMetric (numeratorOf)
open RationalNonnegativePowerOrder (power_order_preserve)
open RationalNonnegativePowers (fraction_congr fraction_multiply)
open RationalReciprocalPowerTail (reciprocalPower)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def offset (A B M k : PTm n) : PTm n := (A+B*k)*M
def rowWeight (q A B M k r : PTm n) : PTm n := weight q (B*M) (offset A B M k+B*r)
def row (m : ℕ) (q A B M k r : PTm n) : PTm n :=
  multiply (sample (m+1) r M) (rowWeight q A B M k r)

ipra_subst offset
ipra_subst rowWeight [GaussianStirlingAllOrderPairedWeight.subst_weight]
ipra_subst row

theorem offset_positive (A B M k : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] le one (offset A B M k) :=
  positive_product _ _ (le_trans hA (le_add_right A (B*k))) hM

theorem weight_pos_den (q A B M k r : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] le one (pw (offset A B M k+B*r) (succ q)) :=
  power_positive _ _ (le_trans (offset_positive A B M k hA hM) (le_add_right _ _))

theorem weight_nonnegative (q A B M k r : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] le (numeratorOf (rowWeight q A B M k r)).neg (numeratorOf (rowWeight q A B M k r)).pos :=
  nonnegative_of_representation _ _ _ (weight_pos_den q A B M k r hA hM)
    (fraction_represents _ _ (weight_pos_den q A B M k r hA hM))

theorem weight_order (q A B M k r : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hM : Γ ⊢[PRAAx] le one M)
    (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] rationalLE (rowWeight q A B M k r) (reciprocalPower (succ q) k) := by
  have hD := le_trans (offset_positive A B M k hA hM) (le_add_right (offset A B M k) (B*r))
  have cleared : Γ ⊢[PRAAx] le (k*(B*M)) (one*(offset A B M k+B*r)) := by
    unfold offset
    ipra_le Groth.ι (IPRA.Q.mk Γ A)*Groth.ι (IPRA.Q.mk Γ M)+Groth.ι (IPRA.Q.mk Γ B)*Groth.ι (IPRA.Q.mk Γ r)
  have lo := power_order_preserve (B*M) (offset A B M k+B*r) one k (succ q) hD hk
    (fraction_order _ _ _ _ hD hk cleared)
  exact rationalLE_congr (.eqRefl _) (fraction_congr (AnalyticNumberTheory.Order.pw_one_base _) (.eqRefl _)) lo

theorem multiply_zero_right (w : PTm n) : Γ ⊢[PRAAx] multiply w (fraction zero one) ≐ fraction zero one := by
  have hD := RationalArgmin.denominator_positive (Γ := Γ) w
  have e := RationalRepresentations.represents_multiply _ _ _ _ _ _
    (RationalRepresentations.represents_self (Γ := Γ) w) (fraction_represents zero one (le_refl one))
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalArithmetic.multiply_guard _ _) (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    e (fraction_represents zero one (le_refl one)) (positive_product _ _ hD (le_refl _)) (le_refl one)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_zero,map_zero]
  ring

theorem row_envelope (m : ℕ) (q A B M k r : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hM : Γ ⊢[PRAAx] le one M) (hk : Γ ⊢[PRAAx] le one k) (hr : Γ ⊢[PRAAx] le r M) :
    Γ ⊢[PRAAx] rationalLE (fraction zero one) (row m q A B M k r) ⋏
      rationalLE (row m q A B M k r) (multiply (cap m) (reciprocalPower (succ q) k)) := by
  let w := rowWeight q A B M k r
  let v := sample (m+1) r M
  have hw := weight_nonnegative q A B M k r hA hM
  have hv := sample_envelope m r M hM hr
  have hc := nonnegative_of_lower (Γ := Γ) (fraction zero one) (cap m)
    (nonnegative_of_representation _ _ _ (le_refl one) (fraction_represents zero one (le_refl one)))
    (GaussianStirlingAllOrderBernoulliEnvelope.cap_nonnegative m)
  have lo := RationalArithmetic.multiply_monotone w _ v hw hv.andE₁
  have hi := RationalArithmetic.multiply_monotone w v (cap m) hw hv.andE₂
  have hi' := RationalArithmetic.multiply_monotone (cap m) w _ hc (weight_order q A B M k r hA hM hk)
  exact .andI (rationalLE_congr (multiply_zero_right w) (multiply_commutative w v) lo)
    (transitive (rationalLE_congr (multiply_commutative w v) (multiply_commutative w (cap m)) hi) hi')

private theorem reflect_scaled (B M r : PTm n) (hr : Γ ⊢[PRAAx] le r M) :
    Γ ⊢[PRAAx] B*monus M r ≐ monus (B*M) (B*r) := by
  have h := mul_le_mul_left B hr
  have ex := natEq (eq_add_of_le hr)
  have ey := natEq (eq_add_of_le h)
  apply deriveNat
  ipra_simps
  linear_combination ey-Groth.ι (IPRA.Q.mk Γ B)*ex

theorem reflected_rows (m : ℕ) (q A B M k r : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hr : Γ ⊢[PRAAx] le r M) :
    Γ ⊢[PRAAx] add (row m q A B M k r) (row m q A B M k (monus M r)) ≐
      multiply (sample (m+1) r M) (pairWeight q (B*M) (offset A B M k) (B*r)) := by
  let v := sample (m+1) r M
  let w := rowWeight q A B M k r
  let w' := weight q (B*M) (offset A B M k+monus (B*M) (B*r))
  have ea : Γ ⊢[PRAAx] rowWeight q A B M k (monus M r) ≐ w' :=
    fraction_congr (.eqRefl _) (congrAp2 powF (.eqRefl _) (congrAdd (.eqRefl _) (reflect_scaled B M r hr)))
  exact (add_congr (.eqRefl (multiply v w)) (multiply_congr (reflected_sample (m+1) r M hM hr) ea)).eqTrans
    (multiply_add v w w').eqSymm

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderKernel
