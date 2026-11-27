import IPRADerivations.Analysis.Stirling.AllOrders.Truncation.CentralTaylor.GaussianStirlingAllOrderCentralTaylor

/-!
# Finite mesh error for the integer central Taylor expansion

The centered second-difference error of the literal polynomial
has a two-sided signed bound with four fewer powers of the mesh
denominator. The bound is uniform at each interior row of the panel.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderCentralTaylorBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingAllOrderCentralTaylor (quadratic homogeneous curvature remainder evenTailTerm central_polynomial)
open BernoulliBounds (pv zint toZ_zint natAbs_cast_of_nonneg natAbs_cast_of_neg)
open GaussianFactorBudget (power_monotone_length)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Finset Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def radiusCoefficient (d : ℕ) (a : Fin (d+1) → ℤ) : ℕ :=
  ∑ j : Fin (d+1), ∑ k ∈ range ((j : ℕ)+1), (a j).natAbs*(2*(j : ℕ).choose k)

def curvatureNumerator (d : ℕ) (a : Fin (d+1) → ℤ) (p M : PTm n) : ZT n :=
  ZT.sumFin fun j => zint (a j*(quadratic (j : ℕ) : ℤ)) *
    ZT.ofNat (pw p (num ((j : ℕ)-2))*pw M (num (d-(j : ℕ))))

def defect (d : ℕ) (a : Fin (d+1) → ℤ) (p M : PTm n) : ZT n :=
  pv a (p+one) M + pv a (monus p one) M - ZT.ofNat two*pv a p M - curvatureNumerator d a p M

theorem evaluation (d : ℕ) (a : Fin (d+1) → ℤ) (p M : PTm n) :
    ZT.toZ Γ (pv a p M) = homogeneous d a (𝔞 p) (𝔞 M) := by
  simp only [pv,ZT.toZ_sumFin,ZT.toZ_mul,toZ_zint,ZT.toZ_ofNat,homogeneous,
    IPRA.Q.mk_mul,map_mul,AnalyticNumberTheory.RobinThreePos.pw_lit]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem curvature_evaluation (d : ℕ) (a : Fin (d+1) → ℤ) (p M : PTm n) :
    ZT.toZ Γ (curvatureNumerator d a p M) = curvature d a (𝔞 p) (𝔞 M) := by
  simp only [curvatureNumerator,ZT.toZ_sumFin,ZT.toZ_mul,toZ_zint,ZT.toZ_ofNat,curvature,
    IPRA.Q.mk_mul,map_mul,AnalyticNumberTheory.RobinThreePos.pw_lit,Int.cast_mul,Int.cast_natCast]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem defect_evaluation (d : ℕ) (a : Fin (d+1) → ℤ) (p M : PTm n) (hp : Γ ⊢[PRAAx] le one p) :
    ZT.toZ Γ (defect d a p M) = remainder d a (𝔞 p) 1 (𝔞 M) := by
  have e := natEq (eq_add_of_le hp)
  ipra_simps
  have h : 𝔞(monus p one) = 𝔞 p-1 := by linear_combination -e
  simp only [defect,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat,evaluation,curvature_evaluation,h]
  ipra_simps
  have e' := central_polynomial d a (𝔞 p) (1:Groth (IPRA.Q Γ)) (𝔞 M)
  norm_num at e' ⊢
  exact e'

private theorem cell_power (d j k : ℕ) (p M : PTm n)
    (hj : j≤d) (hk : k≤j) (h₄ : 4≤k) (hM : Γ ⊢[PRAAx] le one M) (hp : Γ ⊢[PRAAx] le p M) :
    Nonneg Γ ((𝔞 M)^(d-4)-(𝔞 p)^(j-k)*(𝔞 M)^(d-j)) := by
  have em : j-k+(d-j)=d-k := by omega
  have eu : Γ ⊢[PRAAx] pw M (num (j-k))*pw M (num (d-j)) ≐ pw M (num (d-k)) := by
    refine (pw_add M _ _).eqSymm.eqTrans (congrAp2 powF ?_ (.eqRefl M))
    apply deriveNat
    ipra_simps
    simpa only [Nat.cast_add] using congrArg (fun z : ℕ => (z : Groth (IPRA.Q Γ))) em
  have ht := le_trans (le_congr (.eqRefl _) eu (le_mul_mono (pw_le_pw (num (j-k)) hp) (le_refl _)))
    (power_monotone_length M (num (d-k)) (num (d-4)) hM (Foundations.NumeralPrimes.num_le (by omega)))
  simpa only [sl_def,IPRA.Q.mk_mul,map_mul,AnalyticNumberTheory.RobinThreePos.pw_lit] using nn_sl ht

private theorem cell_upper (d : ℕ) (a : Fin (d+1) → ℤ) (p M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hp : Γ ⊢[PRAAx] le p M) (j : Fin (d+1)) (k : ℕ) (hk : k ∈ range ((j : ℕ)+1)) :
    Nonneg Γ (((a j).natAbs : Groth (IPRA.Q Γ))*((2*(j : ℕ).choose k : ℕ):Groth (IPRA.Q Γ))*(𝔞 M)^(d-4) -
       (a j : Groth (IPRA.Q Γ))*evenTailTerm (j : ℕ) k (𝔞 p) 1*(𝔞 M)^(d-(j : ℕ))) := by
  let b : ℕ := 2*(j : ℕ).choose k
  have hPow (ℓ : ℕ) (u : PTm n) : Nonneg Γ ((𝔞 u)^ℓ) := by
    simpa only [AnalyticNumberTheory.RobinThreePos.pw_lit] using nn_term (Γ := Γ) (pw u (num ℓ))
  have hc : Nonneg Γ (((a j).natAbs : Groth (IPRA.Q Γ))*(b : Groth (IPRA.Q Γ))) :=
    nn_mul (nn_natCast _) (nn_natCast _)
  by_cases hk' : 4≤k ∧ Even k
  · have e := cell_power d (j : ℕ) k p M (by omega) (by have := mem_range.mp hk; omega) hk'.1 hM hp
    simp only [evenTailTerm,if_pos hk',one_pow,_root_.mul_one]
    by_cases sign : 0≤a j
    · have r := nn_mul hc e
      convert r using 1
      dsimp only [b]
      simp only [Nat.cast_mul]
      rw [natAbs_cast_of_nonneg sign]
      ring
    · have r := nn_mul hc (nn_add (hPow (d-4) M) (nn_mul (hPow ((j : ℕ)-k) p) (hPow (d-(j : ℕ)) M)))
      convert r using 1
      dsimp only [b]
      simp only [Nat.cast_mul]
      rw [natAbs_cast_of_neg (lt_of_not_ge sign)]
      ring
  · simpa only [evenTailTerm,if_neg hk',MulZeroClass.mul_zero,MulZeroClass.zero_mul,_root_.sub_zero,b] using nn_mul hc (hPow (d-4) M)

theorem upper (d : ℕ) (a : Fin (d+1) → ℤ) (p M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hp : Γ ⊢[PRAAx] le p M) (hlo : Γ ⊢[PRAAx] le one p) :
    Γ ⊢[PRAAx] zle (defect d a p M) (ZT.ofNat (num (radiusCoefficient d a)*pw M (num (d-4)))) := by
  let witness : Groth (IPRA.Q Γ) :=
    ∑ j : Fin (d+1), ∑ k ∈ range ((j : ℕ)+1),
      (((a j).natAbs : Groth (IPRA.Q Γ))*((2*(j : ℕ).choose k : ℕ):Groth (IPRA.Q Γ))*(𝔞 M)^(d-4) -
       (a j : Groth (IPRA.Q Γ))*evenTailTerm (j : ℕ) k (𝔞 p) 1*(𝔞 M)^(d-(j : ℕ)))
  refine zle_of_comb witness ?_ ?_
  · rw [defect_evaluation d a p M hlo]
    have ew : witness = ((radiusCoefficient d a : ℕ):Groth (IPRA.Q Γ))*(𝔞 M)^(d-4)-remainder d a (𝔞 p) 1 (𝔞 M) := by
      unfold witness radiusCoefficient remainder
      push_cast
      simp only [Finset.sum_mul,Finset.mul_sum,Finset.sum_sub_distrib]
    rw [ew]
    ipra_simps
    simp only [AnalyticNumberTheory.RobinThreePos.pw_lit]
  · exact nn_sum _ _ (fun j _ => nn_sum _ _ (fun k hk => cell_upper d a p M hM hp j k hk))

theorem lower (d : ℕ) (a : Fin (d+1) → ℤ) (p M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hp : Γ ⊢[PRAAx] le p M) (hlo : Γ ⊢[PRAAx] le one p) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat (num (radiusCoefficient d a)*pw M (num (d-4)))) (defect d a p M) := by
  let b : Fin (d+1) → ℤ := fun j => -a j
  have hu := upper d b p M hM hp hlo
  refine zle_of_comb (zsl hu) ?_ (nn_zsl hu)
  have er : radiusCoefficient d b = radiusCoefficient d a := by simp [radiusCoefficient,b]
  have ed : remainder d b (𝔞 p) 1 (𝔞 M) = -remainder d a (𝔞 p) 1 (𝔞 M) := by
    simp [remainder,b,Finset.sum_neg_distrib]
  simp only [zsl_def,ZT.toZ_neg,defect_evaluation d a p M hlo,defect_evaluation d b p M hlo,ed,er]
  ring

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderCentralTaylorBound
