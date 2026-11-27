import IPRADerivations.AnalyticNumberTheory.SieveWeightAbs
import IPRADerivations.AnalyticNumberTheory.SieveWeightStep
import IPRADerivations.Foundations.StrongInduction

/-!
# The weight bound of the Selberg sieve

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, `eq:weight-bound`:
"`|λ_d| ≤ 1`, `Σ_{d ∈ D} |λ_d| ≤ |D| ≤ z`".

In the cleared normalization (`A = z! G`, `|Y_r| = Y⁺_r + Y⁻_r`, `W_D = Σ_{r ≤ z} [r ≥ 1] [D ∣ r] |Y_r|`) this module
derives, for `q ≥ 1`,

  `D · W_D ≤ A`   for every `D`                                                       (`point_bound`),
  `Σ_{d ≤ z} (λ⁺_d + λ⁻_d) ≤ z · A`                                                   (`weight_bound`),

the second from the first by `SieveWeightAbs.weights_le`. The first is `|λ_D| ≤ 1`.

The paper proves `|λ_d| ≤ 1` from the closed form `eq:weight-formula` and an injection over all divisors of `d`.
Here it is a strong induction on `D` (`Foundations/StrongInduction`): `D = 0` is trivial, `D = 1` is
`W_1 ≤ Σ_r |Y_r| = A`, and for `D ≥ 2` with `p` the least prime factor of `D` and `D = D' p`,

  `D · W_D = D' · (p · W_{D' p}) ≤ D' · W_{D'} ≤ A`

by the prime step `SieveWeightStep.prime_step` and the induction hypothesis at `D' < D`. No case distinction on
`p ∣ D'` is needed: the prime step holds for every `D' ≥ 1`.

The step function of `strong_ind` is quantified over all contexts and cannot assume `q ≥ 1`, so the violation term
`vB` carries the factor `[q ≥ 1]`: `((D · W_D) ∸ A) · sg(q)`.

* `wS_add`: `W_D` as one sum over `|Y_r|`;
* `W1_le`: the case `D = 1`;
* `ind_alg`, `ind_drop`, `unit_r`: certificates over opaque terms;
* `bound_step`, `v_step`: the induction step.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightBound

open_ipra exports
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrSg zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveDiagonal (Ab Ab_at)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveExpansion (lB)
open LeanProofs.IPRA.AnalyticNumberTheory.SievePrimes (sg_le_one eqb_le1)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightValues (YP YN)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightAbs (wS inst2_wS mul_le_one weights_le)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightStep (habs hv Ab_h prime_step zero_le_of)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Certificates over opaque terms -/

alias dist3 := LeanProofs.IPRA.mul_add

theorem ind_drop {k h : PTm n} (hk : Γ ⊢[PRAAx] le k one) : Γ ⊢[PRAAx] le (k * h) h := by
  ipra_le 𝔞 h * sl hk

/-- `N · W_N ≤ A` from `N = D p`, the prime step `p · W_{Dp} ≤ W_D` and `D · W_D ≤ A`. -/
theorem ind_alg {N D p WN WDp WD A : PTm n} (eN : Γ ⊢[PRAAx] N ≐ D * p) (eW : Γ ⊢[PRAAx] WN ≐ WDp)
    (st : Γ ⊢[PRAAx] le (p * WDp) WD) (ih : Γ ⊢[PRAAx] le (D * WD) A) : Γ ⊢[PRAAx] le (N * WN) A := by
  have x1 := natEq eN; have x2 := natEq eW
  ipra_le sl ih + 𝔞 D * sl st with -(𝔞 WN * x1) - 𝔞 D * 𝔞 p * x2

theorem unit_r {m s : PTm n} (h : Γ ⊢[PRAAx] m * s ≐ zero) (hs : Γ ⊢[PRAAx] s ≐ one) : Γ ⊢[PRAAx] m ≐ zero := by
  ipra_lc natEq h - 𝔞 m * natEq hs

/-- `[q ≥ 1] = 1` for `q ≥ 1`. -/
alias sg_q := Common.sg_of_one_le

/-! ## `W_D` as one sum, and the case `D = 1` -/

/-- `W_D = Σ_{r ≤ z} [r ≥ 1] [D ∣ r] |Y_r|`. -/
theorem wS_add (D P : PTm n) :
    Γ ⊢[PRAAx] inst2 (wS YP) D P + inst2 (wS YN) D P ≐ inst2 (wS habs) D P := by
  rw [inst2_wS, inst2_wS, inst2_wS]
  refine (sum_add2 _ _ _ (.allI (.impI ?_))).eqSymm
  simp only [shift_pairT]
  exact (Ab_h _ _ _).eqTrans ((dist3 _ _ _).eqTrans (congrAdd (Ab_at YP _ _ _).eqSymm (Ab_at YN _ _ _).eqSymm))

/-- `1 · W_1 ≤ A`. -/
theorem W1_le (P : PTm n) : Γ ⊢[PRAAx] le (one * inst2 (wS habs) one P) (Asum P) := by
  rw [inst2_wS]
  have s : Γ ⊢[PRAAx] le (ap2 (sumF (Ab habs)) (succ (sndT (sndT P))) (pairT one P))
      (ap2 (sumF habs) (succ (sndT (sndT P))) P) := by
    refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
    have s1 : Syn.shift (pairT one P) = pairT one (Syn.shift P) := by simp [Syn.shift]
    rw [s1, inst2_addBody]
    exact le_congr (Ab_h _ _ _).eqSymm (.eqRefl _) (ind_drop (mul_le_one (sg_le_one _) (eqb_le1 _ _)))
  exact le_congr (one_mul _).eqSymm (sum_add YP YN _ _) s

/-! ## The induction -/

/-- The violation term `((D · W_D) ∸ A) · [q ≥ 1]` over `0 = D`, `1 = P`. -/
def vB : PTm 2 := monus (var 0 * wS habs) (Asum (var 1)) * sg (fstT (var 1))

theorem inst2_vB (D P : PTm n) :
    inst2 vB D P = monus (D * inst2 (wS habs) D P) (Asum P) * sg (fstT P) := by
  simp [inst2, vB]

/-- The induction step for `q ≥ 1`. -/
theorem bound_step {N P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P))
    (hV : Γ ⊢[PRAAx] ap2 (sumF vB) N P ≐ zero) :
    Γ ⊢[PRAAx] le (N * inst2 (wS habs) N P) (Asum P) := by
  refine .orE (zero_or_succ N) ?_ ?_
  · exact zero_le_of (zero_mul_l Prf.hyp0 _)
  · refine .orE (zero_or_succ (pred N)) ?_ ?_
    · have e : ((pred N ≐ zero) :: (N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] N ≐ one :=
        Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      exact le_congr (congrMul e.eqSymm (congrInst2 (wS habs) e.eqSymm (.eqRefl _))) (.eqRefl _) (W1_le P)
    · let C : List (Fm PTm n) := (pred N ≐ succ (pred (pred N))) :: (N ≐ succ (pred N)) :: Γ
      have hN1 : C ⊢[PRAAx] N ≐ succ (pred N) := Prf.hyp1
      have e : C ⊢[PRAAx] N ≐ succ (succ (pred (pred N))) := Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      have hN2 : C ⊢[PRAAx] le two N :=
        le_of_eq_add (d := pred (pred N)) (e.eqTrans (by ipra_ring))
      have hp := lpf_prime' hN2
      have hpd := lpf_dvd' hN2
      have hp2 := prime_two hp
      have hp1 := p_pos hp2
      have eN : C ⊢[PRAAx] N ≐ lpf N * quo N (lpf N) := eq_of_dvd' hp1 hpd
      have hD : C ⊢[PRAAx] quo N (lpf N) ≐ succ (pred (quo N (lpf N))) := by
        refine .orE (zero_or_succ (quo N (lpf N))) ?_ Prf.hyp0
        have z : ((quo N (lpf N) ≐ zero) :: C) ⊢[PRAAx] N ≐ zero :=
          eN.wk.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))
        exact succ_ne_zero' _ (hN1.wk.eqSymm.eqTrans z)
      have hlt : C ⊢[PRAAx] lt (quo N (lpf N)) N := by
        refine le_of_eq_add (d := monus (lpf N) two * quo N (lpf N) + pred (quo N (lpf N))) ?_
        ipra_lc natEq eN + 𝔞 (quo N (lpf N)) * natEq (eq_add_of_le hp2) + natEq hD
      have ih0 := sum_zero_elim vB hV.wk.wk hlt
      rw [inst2_vB] at ih0
      have ih1 : C ⊢[PRAAx] monus (quo N (lpf N) * inst2 (wS habs) (quo N (lpf N)) P) (Asum P) ≐ zero :=
        unit_r ih0 (sg_q hq.wk.wk)
      rw [inst2_wS] at ih1
      have ih : C ⊢[PRAAx] le (quo N (lpf N) * ap2 (sumF (Ab habs)) (succ (sndT (sndT P)))
          (pairT (quo N (lpf N)) P)) (Asum P) := ih1
      have st := prime_step (Γ := C) hq.wk.wk hp hD
      have eNp : C ⊢[PRAAx] N ≐ quo N (lpf N) * lpf N := eN.eqTrans (mul_comm _ _)
      have eW : C ⊢[PRAAx] inst2 (wS habs) N P ≐
          ap2 (sumF (Ab habs)) (succ (sndT (sndT P))) (pairT (quo N (lpf N) * lpf N) P) := by
        rw [inst2_wS]
        exact congrAp2 (sumF (Ab habs)) (.eqRefl _) (congrPairT eNp (.eqRefl _))
      exact ind_alg eNp eW st ih

/-- The step of the strong induction: the violation at `N` vanishes when all violations below `N` do. -/
theorem v_step {k : ℕ} {Δ : List (Fm PTm k)} (N x : PTm k) (hV : Δ ⊢[PRAAx] ap2 (sumF vB) N x ≐ zero) :
    Δ ⊢[PRAAx] inst2 vB N x ≐ zero := by
  rw [inst2_vB]
  refine .orE (zero_or_succ (fstT x)) ?_ ?_
  · have s0 : ((fstT x ≐ zero) :: Δ) ⊢[PRAAx] sg (fstT x) ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    exact (congrMul (.eqRefl _) s0).eqTrans (mul_zero _)
  · have hq : ((fstT x ≐ succ (pred (fstT x))) :: Δ) ⊢[PRAAx] le one (fstT x) :=
      DiophantineNumberTheory.Coprime.one_le_of_pos Prf.hyp0
    have h0 : ((fstT x ≐ succ (pred (fstT x))) :: Δ) ⊢[PRAAx]
        monus (N * inst2 (wS habs) N x) (Asum x) ≐ zero := bound_step hq hV.wk
    exact zero_mul_l h0 _

/-! ## The bounds -/

/-- `|λ_D| ≤ 1` in the cleared normalization: `D · W_D ≤ A` for `q ≥ 1`. -/
theorem point_bound {D P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P)) :
    Γ ⊢[PRAAx] le (D * (inst2 (wS YP) D P + inst2 (wS YN) D P)) (Asum P) := by
  have h := strong_ind (Γ := Γ) vB (fun N x hV => v_step N x hV) D P
  rw [inst2_vB] at h
  have m : Γ ⊢[PRAAx] le (D * inst2 (wS habs) D P) (Asum P) := unit_r h (sg_q hq)
  exact le_congr (congrMul (.eqRefl _) (wS_add D P).eqSymm) (.eqRefl _) m

/-- `eq:weight-bound` in the cleared normalization: `Σ_{d ≤ z} (λ⁺_d + λ⁻_d) ≤ z · A` for `q ≥ 1`. -/
theorem weight_bound (X : PTm n) {P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P)) :
    Γ ⊢[PRAAx] le
      (ap2 (sumF (sndB (lB UPw))) (succ (sndT (sndT P))) (pairT X P) +
        ap2 (sumF (sndB (lB UNw))) (succ (sndT (sndT P))) (pairT X P))
      (sndT (sndT P) * Asum P) :=
  weights_le X hq (fun _ _ hq' _ => point_bound hq')

end LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightBound
