import IPRADerivations.Analysis.Stirling.AllOrders.Bernoulli.GaussianStirlingAllOrderBernoulliShapeClearing
import IPRADerivations.Analysis.Polynomials.PolynomialBisection

/-!
# Actual monotonicity of the centered Bernoulli half-grid

The lower-half polynomial argument 4t(1-t) increases on the original
mesh. The positive coefficients of the symbolic shape then yield
an object-arithmetic order on its literal canonical rational readings.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliMeshOrder

open_ipra
open GaussianStirlingAllOrderBernoulliShapeClearing (degree scale scale_positive coefficient value left right cleared_identity)
open GaussianStirlingAllOrderCenteredBernoulli (denominator denominator_positive numerator sample sample_value endpoint_samples_zero)
open GaussianStirlingAllOrderBernoulliMesh (toZ_value)
open BernoulliBounds (toZ_zint)
open GaussianRationalHorner (positive_product)
open RationalArgmin (rationalLE rationalLE_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def shapeInput (p M : PTm n) : PTm n := num 4*p*monus M p
noncomputable def shapeDen (m : ℕ) (M : PTm n) : PTm n := num (scale m)*pw (M*M) (num (degree m))

private theorem difference_value (p M : PTm n) (h : Γ ⊢[PRAAx] le p M) :
    𝔞(monus M p) = 𝔞 M-𝔞 p := by
  have e := natEq (eq_add_of_le h)
  simp only [IPRA.Q.mk_add,map_add] at e
  linear_combination -e

private theorem half_le_mesh (p M : PTm n) (h : Γ ⊢[PRAAx] le (two*p) M) : Γ ⊢[PRAAx] le p M :=
  le_trans (le_congr (.eqRefl _) (by ipra_ring) (le_add_right p p)) h

theorem shape_input_monotone (p q M : PTm n) (h : Γ ⊢[PRAAx] le p q)
    (hq : Γ ⊢[PRAAx] le (two*q) M) :
    Γ ⊢[PRAAx] le (shapeInput p M) (shapeInput q M) := by
  have hB := half_le_mesh q M hq
  have hA := le_trans h hB
  have hSum : Γ ⊢[PRAAx] le (p+q) M := by ipra_le sl h+sl hq
  unfold shapeInput
  ipra_le 4*sl h*sl hSum using
    rw [difference_value p M hA,difference_value q M hB]
    ring

theorem shape_den_positive (m : ℕ) (M : PTm n) (h : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] le one (shapeDen m M) :=
  positive_product _ _ (Foundations.NumeralPrimes.num_le (a := 1) (scale_positive m))
    (GaussianFactorBudget.power_positive _ _ (positive_product _ _ h h))

theorem numerator_identity (m : ℕ) (p M : PTm n) (h : Γ ⊢[PRAAx] le p M) :
    𝔞(shapeDen m M)*ZT.toZ Γ (numerator (m+1) p M) =
      𝔞(denominator (m+1) M)*value m (𝔞(shapeInput p M)) (𝔞(M*M)) := by
  have hc := cleared_identity m (𝔞 p) (𝔞 M)
  unfold left right at hc
  unfold shapeDen denominator numerator shapeInput
  simp only [ZT.toZ_mul,ZT.toZ_sub,toZ_zint,toZ_value,IPRA.Q.mk_mul,map_mul,IPRA.Q.mk_num,map_natCast,
    IPRA.Q.mk_zero,map_zero,AnalyticNumberTheory.RobinThreePos.pw_lit,difference_value p M h]
  exact hc

private theorem value_monotone (m : ℕ) (A B D : PTm n) (h : Γ ⊢[PRAAx] le A B) :
    Nonneg Γ (value m (𝔞 B) (𝔞 D)-value m (𝔞 A) (𝔞 D)) := by
  unfold value
  rw [← Finset.sum_sub_distrib]
  apply nn_sum
  intro i _
  have e : Nonneg Γ ((𝔞 B)^(i : ℕ)-(𝔞 A)^(i : ℕ)) := by
    have hpow := pw_le_pw (num (i : ℕ)) h
    simpa only [sl_def,AnalyticNumberTheory.RobinThreePos.pw_lit] using nn_sl hpow
  convert nn_mul (nn_mul (nn_natCast (Γ := Γ) (coefficient m i)) e)
    (nn_pow (nn_term D) (degree m-(i : ℕ))) using 1
  ring

theorem numerator_monotone (m : ℕ) (p q M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (h : Γ ⊢[PRAAx] le p q) (hq : Γ ⊢[PRAAx] le (two*q) M) :
    Γ ⊢[PRAAx] zle (numerator (m+1) p M) (numerator (m+1) q M) := by
  have hB := half_le_mesh q M hq
  have hA := le_trans h hB
  let D := denominator (m+1) M
  let C := shapeDen m M
  apply PolynomialBisection.zle_scale_cancel (c := C) (shape_den_positive m M hM)
  apply zle_of_comb (𝔞 D*(value m (𝔞(shapeInput q M)) (𝔞(M*M))-value m (𝔞(shapeInput p M)) (𝔞(M*M))))
  · simp only [ZT.toZ_mul,ZT.toZ_ofNat,C,numerator_identity m p M hA,numerator_identity m q M hB,D]
    ring
  · exact nn_mul (nn_term D) (value_monotone m _ _ _ (shape_input_monotone p q M h hq))

theorem sample_monotone (m : ℕ) (p q M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (h : Γ ⊢[PRAAx] le p q) (hq : Γ ⊢[PRAAx] le (two*q) M) :
    Γ ⊢[PRAAx] rationalLE (sample (m+1) p M) (sample (m+1) q M) := by
  let D := denominator (m+1) M
  have hD := denominator_positive (m+1) M hM
  apply RationalArithmetic.order_of_representations _ _ _ _ D D (sample_value (m+1) p M hM) (sample_value (m+1) q M hM) hD hD
  have hn := numerator_monotone m p q M hM h hq
  apply zle_of_comb (𝔞 D*zsl hn)
  · simp only [ZT.toZ_mul,ZT.toZ_ofNat,zsl_def]
    ring
  · exact nn_mul (nn_term D) (nn_zsl hn)

theorem sample_nonnegative_first_half (m : ℕ) (p M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hp : Γ ⊢[PRAAx] le (two*p) M) :
    Γ ⊢[PRAAx] rationalLE (GaussianEuclideanDistanceName.fraction zero one) (sample (m+1) p M) :=
  rationalLE_congr (endpoint_samples_zero (m+1) M hM).1 (.eqRefl _) (sample_monotone m zero p M hM (zero_le _) hp)

theorem actual_positive_coefficient_Bernoulli_mesh_order_closed (m : ℕ) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le one (var 2) ⋏ (le (var 0) (var 1) ⋏ le (two*var 1) (var 2))) ⟶
      rationalLE (sample (m+1) (var 0) (var 2)) (sample (m+1) (var 1) (var 2))) :=
  closeUniv 3 (.impI (sample_monotone m _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliMeshOrder
