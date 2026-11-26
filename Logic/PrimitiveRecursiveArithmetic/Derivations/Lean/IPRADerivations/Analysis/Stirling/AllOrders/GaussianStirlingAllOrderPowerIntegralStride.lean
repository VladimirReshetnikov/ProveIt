import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderPowerIntegral
import IPRADerivations.Algebra.PowerDifference

/-!
# Antiderivative bounds across a natural stride

For each positive inverse-power exponent greater than one, the
difference of rational antiderivative values between two natural
numerators is bounded by the stride times the endpoint samples.
The proof uses the finite power-difference sum and keeps the stride
and exponent internal.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPowerIntegralStride

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.PowerDifference (gd gd_succ gd_zero gd_le power_diff)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ConciseIPRA.PTm (zero succ)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianFactorBudget (power_positive)
open GaussianRationalHorner (scalar_congr)
open GaussianRationalMetric (comparison_of_cleared)
open RationalAlgebra (positive_product)
open RationalArithmetic (add represents)
open RationalArgmin (rationalLE)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

private def lo (q k d : PTm n) : Fm PTm n :=
  le (succ q*pw k q) (gd (k+d) k (succ q))

@[simp] private theorem subst_lo {j : ℕ} (σ : Fin n → PTm j) (q k d : PTm n) :
    (lo q k d).subst σ = lo (Syn.subst σ q) (Syn.subst σ k) (Syn.subst σ d) :=
  by simp [lo,pw]

private theorem lo_zero (k d : PTm n) : Γ ⊢[PRAAx] lo zero k d := by
  have z := (gd_succ (Γ := Γ) (k+d) k zero).eqTrans
    ((congrAdd (congrMul (.eqRefl _) (gd_zero _ _)) (.eqRefl _)).eqTrans
      ((congrAdd (mul_zero _) (.eqRefl _)).eqTrans (zero_add _)))
  exact le_congr (one_mul _).eqSymm z.eqSymm (le_refl _)

private theorem lo_succ (q k d : PTm n) (ih : Γ ⊢[PRAAx] lo q k d) :
    Γ ⊢[PRAAx] lo (succ q) k d := by
  have h := le_mul_mono (le_add_right k d) ih
  refine le_congr ?_ (gd_succ _ _ _).eqSymm (add_le_add₂ h (le_refl (pw k (succ q))))
  have e := natEq (pw_succ (Γ := Γ) k q)
  apply deriveNat
  ipra_simps
  linear_combination -(𝔞(q)+1)*e

theorem gd_lower (q k d : PTm n) : Γ ⊢[PRAAx] le (succ q*pw k q) (gd (k+d) k (succ q)) := by
  have all : Γ ⊢[PRAAx] .all (lo (var 0) (Syn.shift k) (Syn.shift d)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_lo,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using lo_zero k d
    · simp only [subst_lo,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact lo_succ _ _ _ Prf.hyp0
  change Γ ⊢[PRAAx] lo q k d
  simpa only [subst_lo,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE q

private theorem lower_native (q k d : PTm n) :
    Γ ⊢[PRAAx] le (k*pw (k+d) (succ q)) (k*pw k (succ q)+d*succ q*pw (k+d) (succ q)) := by
  let W := k+d
  let g := gd W k (succ q)
  have hi : Γ ⊢[PRAAx] le (k*g) (succ q*pw W (succ q)) := by
    refine le_congr (mul_comm _ _) ?_ (le_mul_mono
      (gd_le q (le_refl W) (le_add_right k d)) (le_add_right k d))
    have s := natEq (pw_succ (Γ := Γ) W q)
    apply deriveNat
    dsimp only [W] at s ⊢
    ipra_simps
    linear_combination -(𝔞(q)+1)*s
  have dif := natEq (power_diff (Γ := Γ) W k (succ q))
  ipra_le 𝔞(d)*sl hi using
    dsimp only [W,g] at *
    ipra_simps
    linear_combination (-𝔞(k))*dif

private theorem upper_native (q k d : PTm n) :
    Γ ⊢[PRAAx] le ((k+d)*pw k (succ q)+d*succ q*pw k (succ q)) ((k+d)*pw (k+d) (succ q)) := by
  let W := k+d
  let g := gd W k (succ q)
  have hi : Γ ⊢[PRAAx] le (succ q*pw k (succ q)) (W*g) := by
    refine le_congr ?_ (mul_comm _ _) (le_mul_mono (gd_lower q k d) (le_add_right k d))
    have s := natEq (pw_succ (Γ := Γ) k q)
    apply deriveNat
    ipra_simps
    linear_combination -(𝔞(q)+1)*s
  have dif := natEq (power_diff (Γ := Γ) W k (succ q))
  ipra_le 𝔞(d)*sl hi using
    dsimp only [W,g] at *
    ipra_simps
    linear_combination (𝔞(k)+𝔞(d))*dif

def potential (q k : PTm n) : PTm n := fraction one (succ q*pw k (succ q))

def strideSample (q d k : PTm n) : PTm n := fraction d (pw k (succ (succ q)))

@[simp] theorem subst_potential {j : ℕ} (σ : Fin n → PTm j) (q k : PTm n) :
    Syn.subst σ (potential q k) = potential (Syn.subst σ q) (Syn.subst σ k) := by
  simp [potential,pw]

@[simp] theorem subst_strideSample {j : ℕ} (σ : Fin n → PTm j) (q d k : PTm n) :
    Syn.subst σ (strideSample q d k) = strideSample (Syn.subst σ q) (Syn.subst σ d) (Syn.subst σ k) := by
  simp [strideSample,pw]

private theorem add_fraction_rep (a b c : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hc : Γ ⊢[PRAAx] le one c) :
    Γ ⊢[PRAAx] represents (add (fraction a b) (fraction one c)) (ZT.ofNat (a*c+b)) (b*c) := by
  apply scalar_congr (.eqRefl _) (hAB := .eqRefl _) (h := RationalRepresentations.represents_add _ _ _ _ _ _
    (fraction_represents a b hb) (fraction_represents one c hc))
  apply ZT.derive
  simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  ring

theorem stride_brackets (q k d : PTm n) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] rationalLE (add (strideSample q d (k+d)) (potential q (k+d))) (potential q k) ⋏
      rationalLE (potential q k) (add (strideSample q d k) (potential q (k+d))) := by
  let p := succ q
  let W := k+d
  let K := pw k p
  let V := pw W p
  let K' := pw k (succ p)
  let V' := pw W (succ p)
  have hp : Γ ⊢[PRAAx] le one p := zero_lt_succ q
  have hW := le_trans hk (le_add_right k d)
  have hK := positive_product hp (power_positive k p hk)
  have hV := positive_product hp (power_positive W p hW)
  have hK' := power_positive k (succ p) hk
  have hV' := power_positive W (succ p) hW
  have kpow := natEq (pw_succ (Γ := Γ) k p)
  have vpow := natEq (pw_succ (Γ := Γ) W p)
  have upper : Γ ⊢[PRAAx] le ((p*K)*(d*(p*V)+V')) (one*(V'*(p*V))) := by
    ipra_le 𝔞(p)*𝔞(V)*sl (upper_native q k d) using
      dsimp only [p,W,K,V,V'] at *
      ipra_simps
      rw [vpow]
      ring
  have lower : Γ ⊢[PRAAx] le ((K'*(p*V))*one) ((d*(p*V)+K')*(p*K)) := by
    ipra_le 𝔞(p)*𝔞(K)*sl (lower_native q k d) using
      dsimp only [p,W,K,V,K'] at *
      ipra_simps
      rw [kpow]
      ring
  exact .andI
    (comparison_of_cleared _ _ _ _ _ _ (positive_product hV' hV) hK
      (add_fraction_rep d V' (p*V) hV' hV) (fraction_represents one _ hK)
      upper)
    (comparison_of_cleared _ _ _ _ _ _ hK (positive_product hK' hV)
      (fraction_represents one _ hK) (add_fraction_rep d K' (p*V) hK' hV)
      lower)

theorem actual_reciprocal_power_stride_brackets_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (le one (var 1) ⟶
      rationalLE (add (strideSample (var 0) (var 2) (var 1+var 2)) (potential (var 0) (var 1+var 2)))
          (potential (var 0) (var 1)) ⋏
        rationalLE (potential (var 0) (var 1))
          (add (strideSample (var 0) (var 2) (var 1)) (potential (var 0) (var 1+var 2)))) :=
  closeUniv 3 (.impI (stride_brackets _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPowerIntegralStride
