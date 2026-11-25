import IPRADerivations.AnalyticNumberTheory.FactorialLambda
import IPRADerivations.AnalyticNumberTheory.DivisorSwap
import IPRADerivations.Core.LinearCombination

/-!
# Möbius forms of the weighted von Mangoldt function

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:lambda-mobius`:
for a weight `w` on primes (here with its parameter fixed to `0`),

* `lambda_mobius`: `Λ_w(N) = ∑_{d ∣ N} μ(d) L_w(N/d)` for `N ≥ 1` — Möbius inversion
  (`MobiusInversion.mobius_inversion`) of `∑_{e ∣ k} Λ_w(e) = L_w(k)` (`lambda_divsum`), each row
  `[d ∣ N] μ(d) ∑_{e ∣ N/d} Λ_w(e)` being `[d ∣ N] μ(d) L_w(N/d)` (`row_lam_mob`);
* `lambda_mobius_neg`: `Λ_w(N) = −∑_{d ∣ N} μ(d) L_w(d)` for `N ≥ 2`, from complete additivity
  `L_w(N/d) = L_w(N) − L_w(d)` for `d ∣ N` (`split_pt`) and `∑_{d ∣ N} μ(d) = 0`.

* `lambda_mobius_mid`: `Λ_w(N) = ∑_{d ∣ N} μ(N/d) L_w(d)` for `N ≥ 1`, the first form after the
  divisor involution `d ↔ N/d` (`DivisorSwap.div_swap`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.MangoldtMobius

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (sum_ext shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversion (aP aN inst3_aP inst3_aN mobius_inversion eqb_rem_big)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (DB_at congrLw lw_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' pos_of_eq_mul)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

section Forms

variable (w : PTm 2)

/-- `Λ_w(e)`, over `0 = e` (weight parameter `0`). -/
abbrev lamF : PTm 2 := ap2 (sumF (lamB w)) (succ (var 0)) (pairT (var 0) zero)
/-- `[d ∣ N] μ^±(d) L_w(N/d)`. -/
abbrev QLP : PTm 2 := PB * ap2 (sumF (ellB w)) (succ (quo (var 1) (var 0))) (pairT (quo (var 1) (var 0)) zero)
abbrev QLN : PTm 2 := NB * ap2 (sumF (ellB w)) (succ (quo (var 1) (var 0))) (pairT (quo (var 1) (var 0)) zero)
/-- `[d ∣ N] μ^±(d) L_w(d)`. -/
abbrev RLP : PTm 2 := PB * ap2 (sumF (ellB w)) (succ (var 0)) (pairT (var 0) zero)
abbrev RLN : PTm 2 := NB * ap2 (sumF (ellB w)) (succ (var 0)) (pairT (var 0) zero)

theorem inst2_lamF (e N : PTm n) : inst2 (lamF w) e N = Lam w e zero := by simp [inst2]
theorem inst2_QLP (d N : PTm n) : inst2 (QLP w) d N = ((sg d * eqb (rem N d) zero) * muP (succ N) d) * Lw w (quo N d) zero := by
  simp [inst2]
theorem inst2_QLN (d N : PTm n) : inst2 (QLN w) d N = ((sg d * eqb (rem N d) zero) * muN (succ N) d) * Lw w (quo N d) zero := by
  simp [inst2]
theorem inst2_RLP (d N : PTm n) : inst2 (RLP w) d N = ((sg d * eqb (rem N d) zero) * muP (succ N) d) * Lw w d zero := by
  simp [inst2]
theorem inst2_RLN (d N : PTm n) : inst2 (RLN w) d N = ((sg d * eqb (rem N d) zero) * muN (succ N) d) * Lw w d zero := by
  simp [inst2]

/-- `∑_{e ≤ N} [e ∣ k] Λ_w(e) = L_w(k)` for `1 ≤ k ≤ N`. -/
theorem inner_lam {k N : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) (hkN : Γ ⊢[PRAAx] le (succ k) (succ N)) :
    Γ ⊢[PRAAx] ap2 (sumF (DB w)) (succ N) (pairT k zero) ≐ Lw w k zero := by
  have hk' := shift_pos hk
  have cut : Γ ⊢[PRAAx] ap2 (sumF (DB w)) (succ N) (pairT k zero) ≐ ap2 (sumF (DB w)) (succ k) (pairT k zero) := by
    refine sum_ext (DB w) (fun Δ a hs hl => ?_) hkN
    rw [shift_pairT]
    refine (DB_at w _ _ _).eqTrans (zero_mul_l ?_ _)
    exact (congrMul (.eqRefl _) (eqb_rem_big (hk'.weaken hs) hl)).eqTrans (mul_zero _)
  exact cut.eqTrans (lambda_divsum w hk)

/-- A row of the inversion for `f = Λ_w`: `[d ∣ N] μ^±(d) ∑_{e ∣ N/d} Λ_w(e) = [d ∣ N] μ^±(d) L_w(N/d)`. -/
theorem row_lam_mob {d N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] (inst2 (oB (aP (lamF w))) d (pairT (succ N) N) ≐ inst2 (QLP w) d N) ⋏
      (inst2 (oB (aN (lamF w))) d (pairT (succ N) N) ≐ inst2 (QLN w) d N) := by
  rw [inst2_oB, inst2_oB, inst2_QLP, inst2_QLN]
  have f₁ : Γ ⊢[PRAAx] fstT (pairT (succ N) N) ≐ succ N := fst_pair _ _
  have s₁ : Γ ⊢[PRAAx] sndT (pairT (succ N) N) ≐ N := snd_pair _ _
  have cR := congrAp2 (sumF (rowB (aP (lamF w)))) f₁ (congrPairT (.eqRefl d) s₁)
  have cR' := congrAp2 (sumF (rowB (aN (lamF w)))) f₁ (congrPairT (.eqRefl d) s₁)
  have hcP : Syn.shift ((sg d * eqb (rem N d) zero) * muP (succ N) d) =
      (sg (Syn.shift d) * eqb (rem (Syn.shift N) (Syn.shift d)) zero) * muP (succ (Syn.shift N)) (Syn.shift d) := by
    simp [Syn.shift]
  have hcN : Syn.shift ((sg d * eqb (rem N d) zero) * muN (succ N) d) =
      (sg (Syn.shift d) * eqb (rem (Syn.shift N) (Syn.shift d)) zero) * muN (succ (Syn.shift N)) (Syn.shift d) := by
    simp [Syn.shift]
  have hq : Syn.shift (pairT (quo N d) (zero : PTm n)) = pairT (quo (Syn.shift N) (Syn.shift d)) zero := by
    simp [Syn.shift]
  have scP : Γ ⊢[PRAAx] ap2 (sumF (rowB (aP (lamF w)))) (succ N) (pairT d N) ≐
      ((sg d * eqb (rem N d) zero) * muP (succ N) d) * ap2 (sumF (DB w)) (succ N) (pairT (quo N d) zero) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_rowB, shift_pairT, hcP, hq]
    refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_aP, inst2_lamF]
    exact congrMul (.eqRefl _) (DB_at w _ _ _).eqSymm
  have scN : Γ ⊢[PRAAx] ap2 (sumF (rowB (aN (lamF w)))) (succ N) (pairT d N) ≐
      ((sg d * eqb (rem N d) zero) * muN (succ N) d) * ap2 (sumF (DB w)) (succ N) (pairT (quo N d) zero) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_rowB, shift_pairT, hcN, hq]
    refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_aN, inst2_lamF]
    exact congrMul (.eqRefl _) (DB_at w _ _ _).eqSymm
  have key : ∀ (X : PTm n), Γ ⊢[PRAAx] ((sg d * eqb (rem N d) zero) * X) * ap2 (sumF (DB w)) (succ N) (pairT (quo N d) zero) ≐
      ((sg d * eqb (rem N d) zero) * X) * Lw w (quo N d) zero := by
    intro X
    refine .orE (zero_or_succ d) ?_ ?_
    · have s0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] sg d ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
      exact (zero_mul_l (zero_mul_l (zero_mul_l s0 _) _) _).eqTrans (zero_mul_l (zero_mul_l (zero_mul_l s0 _) _) _).eqSymm
    · refine .orE (eq_or_ne (rem N d) zero) ?_ ?_
      · let C : List (Fm PTm n) := (rem N d ≐ zero) :: (d ≐ succ (pred d)) :: Γ
        have hd : C ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp1
        have eN := eq_of_dvd' hd (Prf.hyp0 : C ⊢[PRAAx] dvd d N)
        have hk := pos_of_eq_mul hN.wk.wk eN
        have ww := natEq eN; have wp := natEq hd
        have hkN : C ⊢[PRAAx] le (succ (quo N d)) (succ N) := by
          refine (succ_monus_succ _ _).eqTrans (le_of_eq_add (d := pred d * quo N d) ?_)
          ipra_lc ww + 𝔞 (quo N d) * wp
        exact congrMul (.eqRefl _) (inner_lam w hk hkN)
      · have z : (neg (rem N d ≐ zero) :: (d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] sg d * eqb (rem N d) zero ≐ zero :=
          (congrMul (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans (by ipra_ring)
        exact (zero_mul_l (zero_mul_l z _) _).eqTrans (zero_mul_l (zero_mul_l z _) _).eqSymm
  exact .andI (cR.eqTrans (scP.eqTrans (key _))) (cR'.eqTrans (scN.eqTrans (key _)))

/-- `thm:lambda-mobius`: `Λ_w(N) = ∑_{d ∣ N} μ(d) L_w(N/d)` for `N ≥ 1`. -/
theorem lambda_mobius {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] ap2 (sumF (QLP w)) (succ N) N ≐ Lam w N zero + ap2 (sumF (QLN w)) (succ N) N := by
  have inv := mobius_inversion (Γ := Γ) (lamF w) hN
  rw [inst2_lamF] at inv
  have hN' := shift_pos hN
  have hs : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  have cP : Γ ⊢[PRAAx] ap2 (sumF (oB (aP (lamF w)))) (succ N) (pairT (succ N) N) ≐ ap2 (sumF (QLP w)) (succ N) N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, hs]
    exact Prf.andE₁ (row_lam_mob w hN'.wk)
  have cN : Γ ⊢[PRAAx] ap2 (sumF (oB (aN (lamF w)))) (succ N) (pairT (succ N) N) ≐ ap2 (sumF (QLN w)) (succ N) N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, hs]
    exact Prf.andE₂ (row_lam_mob w hN'.wk)
  ipra_lc -natEq cP + natEq inv + natEq cN

/-- For `d ∣ N`: `L_w(N/d) + L_w(d) = L_w(N)`, so `[d ∣ N] μ(d) (L_w(N/d) + L_w(d)) = [d ∣ N] μ(d) L_w(N)`. -/
theorem split_pt {d N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] (inst2 (QLP w) d N + inst2 (RLP w) d N ≐ Lw w N zero * inst2 PB d N) ⋏
      (inst2 (QLN w) d N + inst2 (RLN w) d N ≐ Lw w N zero * inst2 NB d N) := by
  rw [inst2_QLP, inst2_RLP, inst2_QLN, inst2_RLN, inst2_PB, inst2_NB]
  refine .orE (zero_or_succ d) ?_ ?_
  · have s0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] sg d ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    have z : ∀ {X Y : PTm n}, ((d ≐ zero) :: Γ) ⊢[PRAAx] ((sg d * eqb (rem N d) zero) * X) * Y ≐ zero :=
      fun {X Y} => zero_mul_l (zero_mul_l (zero_mul_l s0 _) _) _
    have z' : ∀ {X : PTm n}, ((d ≐ zero) :: Γ) ⊢[PRAAx] Lw w N zero * ((sg d * eqb (rem N d) zero) * X) ≐ zero :=
      fun {X} => (congrMul (.eqRefl _) (zero_mul_l (zero_mul_l s0 _) _)).eqTrans (mul_zero _)
    exact .andI ((congrAdd z z).eqTrans ((add_zero _).eqTrans z'.eqSymm))
      ((congrAdd z z).eqTrans ((add_zero _).eqTrans z'.eqSymm))
  · refine .orE (eq_or_ne (rem N d) zero) ?_ ?_
    · let C : List (Fm PTm n) := (rem N d ≐ zero) :: (d ≐ succ (pred d)) :: Γ
      have hd : C ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp1
      have eN := eq_of_dvd' hd (Prf.hyp0 : C ⊢[PRAAx] dvd d N)
      have hk := pos_of_eq_mul hN.wk.wk eN
      have add := (congrLw w zero eN).eqTrans (lw_mul w hd hk)
      have e := natEq add
      refine .andI ?_ ?_ <;> (apply deriveNat; ipra_simps)
      · linear_combination -(𝔞 (sg d) * 𝔞 (eqb (rem N d) zero) * 𝔞 (eqb (sq (succ N) d) zero) *
          𝔞 (eqb (rem (om (succ N) d) two) zero)) * e
      · linear_combination -(𝔞 (sg d) * 𝔞 (eqb (rem N d) zero) * 𝔞 (eqb (sq (succ N) d) zero) *
          𝔞 (eqb (rem (om (succ N) d) two) one)) * e
    · let C : List (Fm PTm n) := neg (rem N d ≐ zero) :: (d ≐ succ (pred d)) :: Γ
      have zz : C ⊢[PRAAx] sg d * eqb (rem N d) zero ≐ zero :=
        (congrMul (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans (by ipra_ring)
      have z : ∀ {X Y : PTm n}, C ⊢[PRAAx] ((sg d * eqb (rem N d) zero) * X) * Y ≐ zero :=
        fun {X Y} => zero_mul_l (zero_mul_l zz _) _
      have z' : ∀ {X : PTm n}, C ⊢[PRAAx] Lw w N zero * ((sg d * eqb (rem N d) zero) * X) ≐ zero :=
        fun {X} => (congrMul (.eqRefl _) (zero_mul_l zz _)).eqTrans (mul_zero _)
      exact .andI ((congrAdd z z).eqTrans ((add_zero _).eqTrans z'.eqSymm))
        ((congrAdd z z).eqTrans ((add_zero _).eqTrans z'.eqSymm))

/-- `thm:lambda-mobius`, third form: `Λ_w(N) = −∑_{d ∣ N} μ(d) L_w(d)` for `N ≥ 2`, as
`Λ_w(N) + ∑_{d ∣ N} μ⁺(d) L_w(d) = ∑_{d ∣ N} μ⁻(d) L_w(d)`. -/
theorem lambda_mobius_neg {N : PTm n} (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] Lam w N zero + ap2 (sumF (RLP w)) (succ N) N ≐ ap2 (sumF (RLN w)) (succ N) N := by
  have hp := pos_of_two hN
  have hN' := shift_pos hp
  have h2 : Syn.shift (Lw w N zero) = Lw w (Syn.shift N) zero := by simp [Syn.shift]
  have sP : Γ ⊢[PRAAx] ap2 (sumF (addBody (QLP w) (RLP w))) (succ N) N ≐ Lw w N zero * ap2 (sumF PB) (succ N) N := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_addBody, h2]
    exact Prf.andE₁ (split_pt w hN'.wk)
  have sN : Γ ⊢[PRAAx] ap2 (sumF (addBody (QLN w) (RLN w))) (succ N) N ≐ Lw w N zero * ap2 (sumF NB) (succ N) N := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_addBody, h2]
    exact Prf.andE₂ (split_pt w hN'.wk)
  have aP' := natEq (sum_add (Γ := Γ) (QLP w) (RLP w) (succ N) N)
  have aN' := natEq (sum_add (Γ := Γ) (QLN w) (RLN w) (succ N) N)
  have lm := natEq (lambda_mobius w hp)
  have mc := natEq (mobius_cancel hN)
  have e₁ := natEq sP; have e₂ := natEq sN
  apply deriveNat; ipra_simps
  linear_combination -lm - aP' + aN' + e₁ - e₂ + 𝔞 (Lw w N zero) * mc

/-- `μ^±_{N+1}(a) L_w(b)`, over `0 = a`, `1 = b`, `2 = N`. -/
abbrev mlP : PTm 3 := muP (succ (var 2)) (var 0) * ap2 (sumF (ellB w)) (succ (var 1)) (pairT (var 1) zero)
abbrev mlN : PTm 3 := muN (succ (var 2)) (var 0) * ap2 (sumF (ellB w)) (succ (var 1)) (pairT (var 1) zero)

theorem inst3_mlP (a b N : PTm n) : inst3 (mlP w) a b N = muP (succ N) a * Lw w b zero := by simp [inst3]
theorem inst3_mlN (a b N : PTm n) : inst3 (mlN w) a b N = muN (succ N) a * Lw w b zero := by simp [inst3]

/-- `thm:lambda-mobius`, middle form: `Λ_w(N) = ∑_{d ∣ N} μ(N/d) L_w(d)` for `N ≥ 1`, as
`∑_{d ∣ N} μ⁺(N/d) L_w(d) = Λ_w(N) + ∑_{d ∣ N} μ⁻(N/d) L_w(d)`. -/
theorem lambda_mobius_mid {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] ap2 (sumF (DivisorSwap.TB (mlP w))) (succ N) N ≐
      Lam w N zero + ap2 (sumF (DivisorSwap.TB (mlN w))) (succ N) N := by
  have cP : Γ ⊢[PRAAx] ap2 (sumF (DivisorSwap.SB (mlP w))) (succ N) N ≐ ap2 (sumF (QLP w)) (succ N) N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [DivisorSwap.inst2_SB, inst3_mlP, inst2_QLP]
    ipra_ring
  have cN : Γ ⊢[PRAAx] ap2 (sumF (DivisorSwap.SB (mlN w))) (succ N) N ≐ ap2 (sumF (QLN w)) (succ N) N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [DivisorSwap.inst2_SB, inst3_mlN, inst2_QLN]
    ipra_ring
  ipra_lc -natEq (DivisorSwap.div_swap (mlP w) hN) + natEq cP + natEq (lambda_mobius w hN) - natEq cN +
    natEq (DivisorSwap.div_swap (mlN w) hN)

end Forms

end LeanProofs.IPRA.AnalyticNumberTheory.MangoldtMobius
