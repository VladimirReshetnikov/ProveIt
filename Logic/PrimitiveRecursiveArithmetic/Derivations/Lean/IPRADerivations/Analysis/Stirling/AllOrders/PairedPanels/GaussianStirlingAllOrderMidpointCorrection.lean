import IPRADerivations.Analysis.Stirling.AllOrders.Bernoulli.GridBounds.GaussianStirlingAllOrderFullGridCovariance

/-!
# Bounds for the exact midpoint correction

Every correction has the factor 1/(4S). The first panel has a
bound in terms of B/A; later panels have summable reciprocal-power
bounds. The same bounds hold at every positive refinement.
-/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderMidpointCorrection

open_ipra
open GaussianEuclideanDistanceName (fraction fraction_order fraction_represents)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (nonnegative_of_lower nonnegative_of_representation)
open GaussianStirlingAllOrderBernoulliEnvelope (cap cap_nonnegative sample_envelope)
open GaussianStirlingAllOrderFullGridCovariance (midpointCorrection)
open GaussianStirlingAllOrderKernel (offset row rowWeight multiply_zero_right offset_positive weight_nonnegative row_envelope)
open GaussianStirlingAllOrderPairedWeight (weight)
open RationalAlgebra (multiply_commutative)
open RationalArgmin (rationalLE rationalLE_congr transitive)
open RationalArithmetic (multiply multiply_monotone)
open RationalNonnegativePowerOrder (power_order_preserve)
open RationalReciprocalPowerTail (reciprocalPower)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "z" => fraction zero one

ipra_subst midpointCorrection

def baseWeight (q A B : PTm n) : PTm n := fraction (pw B (succ q)) (pw A (succ q))
def baseCap (m : ℕ) (q A B : PTm n) : PTm n := multiply (cap m) (baseWeight q A B)
def tailCap (m : ℕ) (q k : PTm n) : PTm n := multiply (cap m) (reciprocalPower (succ q) k)

ipra_subst baseCap [baseWeight, pw]
ipra_subst tailCap

private theorem zero_sign : Γ ⊢[PRAAx] GaussianPositiveRealArithmetic.sign (z : PTm n) :=
  nonnegative_of_representation _ _ _ (le_refl one) (fraction_represents zero one (le_refl one))

private theorem edge_scale (S x y : PTm n) (hS : Γ ⊢[PRAAx] le one S)
    (hx : Γ ⊢[PRAAx] rationalLE z x) (hy : Γ ⊢[PRAAx] rationalLE x y) :
    Γ ⊢[PRAAx] rationalLE z (multiply (fraction one (S*num 4)) x) ⋏
      rationalLE (multiply (fraction one (S*num 4)) x) (multiply (fraction one (S*num 4)) y) := by
  let N := S*num 4
  let c := fraction one N
  have hN : Γ ⊢[PRAAx] le one N := positive_product _ _ hS (by ipra_le 3)
  have hc := nonnegative_of_representation c one N hN (fraction_represents one N hN)
  exact .andI (rationalLE_congr (multiply_zero_right c) (.eqRefl _) (multiply_monotone c _ _ hc hx))
    (multiply_monotone c _ _ hc hy)

theorem midpoint_base_bound (m : ℕ) (q A B S k : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] rationalLE z (midpointCorrection m q A B S k) ⋏
      rationalLE (midpointCorrection m q A B S k) (multiply (fraction one (S*num 4)) (baseCap m q A B)) := by
  let M := S*num 8
  let N := S*num 4
  let D := offset A B M k+B*N
  let h := rowWeight q A B M k N
  let v := GaussianStirlingAllOrderCenteredBernoulli.sample (m+1) N M
  let c : PTm n := cap m
  have hM : Γ ⊢[PRAAx] le one M := positive_product _ _ hS (by ipra_le 7)
  have hNM : Γ ⊢[PRAAx] le N M := by unfold N M; ipra_le 4*𝔞 S
  have hD : Γ ⊢[PRAAx] le one D := le_trans (offset_positive A B M k hA hM) (le_add_right _ _)
  have hcap : Γ ⊢[PRAAx] GaussianPositiveRealArithmetic.sign c :=
    nonnegative_of_lower _ _ zero_sign (cap_nonnegative m)
  have hh := weight_nonnegative q A B M k N hA hM
  have he := sample_envelope m N M hM hNM
  have clear : Γ ⊢[PRAAx] le (A*(B*M)) (B*D) := by
    unfold D offset
    ipra_le 𝔞 B*𝔞 B*𝔞 k*𝔞 M+𝔞 B*𝔞 B*𝔞 N
  have hw : Γ ⊢[PRAAx] rationalLE h (baseWeight q A B) :=
    power_order_preserve (B*M) D B A (succ q) hD hA (fraction_order _ _ _ _ hD hA clear)
  have lo := rationalLE_congr (multiply_zero_right h) (multiply_commutative h v)
    (multiply_monotone h _ _ hh he.andE₁)
  have up := rationalLE_congr (multiply_commutative h v) (multiply_commutative h c)
    (multiply_monotone h v c hh he.andE₂)
  exact edge_scale S _ _ hS lo (transitive up (multiply_monotone c _ _ hcap hw))

theorem midpoint_tail_bound (m : ℕ) (q A B S k : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hS : Γ ⊢[PRAAx] le one S) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] rationalLE z (midpointCorrection m q A B S k) ⋏
      rationalLE (midpointCorrection m q A B S k) (multiply (fraction one (S*num 4)) (tailCap m q k)) := by
  have hM : Γ ⊢[PRAAx] le one (S*num 8) := positive_product _ _ hS (by ipra_le 7)
  have hNM : Γ ⊢[PRAAx] le (S*num 4) (S*num 8) := by ipra_le 4*𝔞 S
  have h := row_envelope m q A B (S*num 8) k (S*num 4) hA hM hk hNM
  exact edge_scale S _ _ hS h.andE₁ h.andE₂

theorem actual_original_midpoint_geometric_mesh_bound_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 1) ⟶ le one (var 3) ⟶
        (rationalLE z (midpointCorrection m (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
         rationalLE (midpointCorrection m (var 0) (var 1) (var 2) (var 3) (var 4))
           (multiply (fraction one (var 3*num 4)) (baseCap m (var 0) (var 1) (var 2))))) :=
  closeUniv 5 (.impI (.impI (midpoint_base_bound m _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderMidpointCorrection
