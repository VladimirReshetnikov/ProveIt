import IPRADerivations.AnalyticNumberTheory.MangoldtMobius
import IPRADerivations.Core.LinearCombination
import IPRADerivations.AnalyticNumberTheory.DivisorCases
import IPRADerivations.Core.Reindex
import IPRADerivations.Core.Header

/-!
# The Möbius–Mangoldt convolution

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:mu-lambda`:
for `N ≥ 1` and every weight `w` (parameter `0`),

  `∑_{d ∣ N} μ(N/d) Λ_w(d) = −μ(N) L_w(N)`   (`mu_lambda`),

written with `μ = μ⁺ − μ⁻` as `∑ μ⁺(N/d) Λ_w(d) + μ⁺(N) L_w(N) = ∑ μ⁻(N/d) Λ_w(d) + μ⁻(N) L_w(N)`.

The proof is the convolution argument `μ * Λ_w = μ * (−μ L_w) * 1 = −μ L_w`: Möbius inversion
(`mobius_inversion`) applied to `f = μ⁻ L_w` and to `f = μ⁺ L_w`, whose divisor sums differ by
exactly `Λ_w` (`key_inner`, the third form of `thm:lambda-mobius` extended to `k = 1` as
`lambda_mobius_neg'`), gives `∑_{d ∣ N} μ(d) Λ_w(N/d) = −μ(N) L_w(N)` (`mu_lambda_conv`); the
divisor involution (`div_swap`) turns it into the stated orientation.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.MuLambda

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (sum_ext shift_pos mu_bound)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversion (aP aN inst3_aP inst3_aN mobius_inversion eqb_rem_big)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.AnalyticNumberTheory.MangoldtMobius
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' pos_of_eq_mul)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `∑_{i < 2} B(i, x) = 0` when both terms vanish. -/
theorem sum_two_zero (B : PTm 2) {x : PTm n} (h0 : Γ ⊢[PRAAx] inst2 B zero x ≐ zero)
    (h1 : Γ ⊢[PRAAx] inst2 B one x ≐ zero) : Γ ⊢[PRAAx] ap2 (sumF B) (succ one) x ≐ zero :=
  (sum_succ' _ _ _).eqTrans ((congrAdd ((sum_succ' _ _ _).eqTrans
    ((congrAdd (sum_zero _ _) h0).eqTrans (zero_add _))) h1).eqTrans (add_zero _))

section MuLambda

variable (w : PTm 2)

/-- `L_w(1) = 0`. -/
theorem lw_one (y : PTm n) : Γ ⊢[PRAAx] Lw w one y ≐ zero :=
  sum_two_zero _ (by rw [inst2_ell]; exact zero_mul_l (zero_mul_l isP_zero _) _)
    (by rw [inst2_ell]; exact zero_mul_l (zero_mul_l isP_one _) _)

/-- `Λ_w(1) = 0`. -/
theorem lam_one (y : PTm n) : Γ ⊢[PRAAx] Lam w one y ≐ zero :=
  sum_two_zero _ (by rw [inst2_lam]; exact zero_mul_l (zero_mul_l isP_zero _) _)
    (by rw [inst2_lam]; exact zero_mul_l (zero_mul_l isP_one _) _)

/-- The third form of `thm:lambda-mobius` for every `k ≥ 1`: at `k = 1` all terms vanish. -/
theorem lambda_mobius_neg' {k : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) :
    Γ ⊢[PRAAx] Lam w k zero + ap2 (sumF (RLP w)) (succ k) k ≐ ap2 (sumF (RLN w)) (succ k) k := by
  refine .orE (lt_or_le one k) (lambda_mobius_neg w Prf.hyp0) ?_
  let C : List (Fm PTm n) := le k one :: Γ
  have k1 : C ⊢[PRAAx] k ≐ one :=
    le_antisymm Prf.hyp0 (le_of_eq_add (d := pred k) (hk.wk.eqTrans (by ipra_ring)))
  have lz : C ⊢[PRAAx] Lam w k zero ≐ zero :=
    (congrAp2 (sumF (lamB w)) (congrSucc k1) (congrPairT k1 (.eqRefl _))).eqTrans (lam_one w _)
  have pz : C ⊢[PRAAx] ap2 (sumF (RLP w)) (succ k) k ≐ zero := by
    refine (congrAp2 (sumF (RLP w)) (congrSucc k1) k1).eqTrans (sum_two_zero _ ?_ ?_) <;> rw [inst2_RLP]
    · exact zero_mul_l (zero_mul_l (zero_mul_l sg_zero _) _) _
    · exact (congrMul (.eqRefl _) (lw_one w _)).eqTrans (mul_zero _)
  have nz : C ⊢[PRAAx] ap2 (sumF (RLN w)) (succ k) k ≐ zero := by
    refine (congrAp2 (sumF (RLN w)) (congrSucc k1) k1).eqTrans (sum_two_zero _ ?_ ?_) <;> rw [inst2_RLN]
    · exact zero_mul_l (zero_mul_l (zero_mul_l sg_zero _) _) _
    · exact (congrMul (.eqRefl _) (lw_one w _)).eqTrans (mul_zero _)
  exact (congrAdd lz pz).eqTrans ((add_zero _).eqTrans nz.eqSymm)

/-! ## Inner divisor sums with the bound `N` -/

/-- `[e ∣ k] f(e, N)`, over `0 = e`, `1 = ⟨k, N⟩`. -/
def ivB (f : PTm 2) : PTm 2 :=
  (sg (var 0) * eqb (rem (fstT (var 1)) (var 0)) zero) * Syn.subst ![var 0, sndT (var 1)] f

theorem inst2_ivB (f : PTm 2) (e z : PTm n) :
    inst2 (ivB f) e z = (sg e * eqb (rem (fstT z) e) zero) * inst2 f e (sndT z) := by
  simp only [inst2, ivB, PTm.subst_mul, subst_reindex2]
  simp

theorem iv_at (f : PTm 2) (e k N : PTm n) :
    Γ ⊢[PRAAx] inst2 (ivB f) e (pairT k N) ≐ (sg e * eqb (rem k e) zero) * inst2 f e N := by
  rw [inst2_ivB]
  exact congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF (fst_pair _ _) (.eqRefl _)) (.eqRefl _)))
    (congrInst2 f (.eqRefl _) (snd_pair _ _))

/-- `μ^±_{N+1}(e) L_w(e)`, over `0 = e`, `1 = N`. -/
abbrev fP : PTm 2 := muP (succ (var 1)) (var 0) * ap2 (sumF (ellB w)) (succ (var 0)) (pairT (var 0) zero)
abbrev fN : PTm 2 := muN (succ (var 1)) (var 0) * ap2 (sumF (ellB w)) (succ (var 0)) (pairT (var 0) zero)

theorem inst2_fP (e N : PTm n) : inst2 (fP w) e N = muP (succ N) e * Lw w e zero := by simp [inst2]
theorem inst2_fN (e N : PTm n) : inst2 (fN w) e N = muN (succ N) e * Lw w e zero := by simp [inst2]

/-- Cutting an inner divisor sum of `k ≤ N` at `k`. -/
theorem iv_cut (f : PTm 2) {k N : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k))
    (hkN : Γ ⊢[PRAAx] le (succ k) (succ N)) :
    Γ ⊢[PRAAx] ap2 (sumF (ivB f)) (succ N) (pairT k N) ≐ ap2 (sumF (ivB f)) (succ k) (pairT k N) := by
  have hk' := shift_pos hk
  refine sum_ext (ivB f) (fun Δ a hs hl => ?_) hkN
  rw [shift_pairT]
  refine (iv_at f _ _ _).eqTrans (zero_mul_l ?_ _)
  exact (congrMul (.eqRefl _) (eqb_rem_big (hk'.weaken hs) hl)).eqTrans (mul_zero _)

/-- Changing the Möbius bound from `N + 1` to `k + 1` for `e ≤ k ≤ N`. -/
theorem rl_pt {e k N : PTm n} (he : Γ ⊢[PRAAx] le (succ e) (succ k)) (hkN : Γ ⊢[PRAAx] le (succ k) (succ N)) :
    Γ ⊢[PRAAx] (inst2 (ivB (fP w)) e (pairT k N) ≐ inst2 (RLP w) e k) ⋏
      (inst2 (ivB (fN w)) e (pairT k N) ≐ inst2 (RLN w) e k) := by
  have a := iv_at (Γ := Γ) (fP w) e k N
  have b := iv_at (Γ := Γ) (fN w) e k N
  rw [inst2_fP] at a
  rw [inst2_fN] at b
  rw [inst2_RLP, inst2_RLN]
  refine .orE (zero_or_succ e) ?_ ?_
  · have s0 : ((e ≐ zero) :: Γ) ⊢[PRAAx] sg e ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    exact .andI ((a.wk.eqTrans (zero_mul_l (zero_mul_l s0 _) _)).eqTrans
        (zero_mul_l (zero_mul_l (zero_mul_l s0 _) _) _).eqSymm)
      ((b.wk.eqTrans (zero_mul_l (zero_mul_l s0 _) _)).eqTrans
        (zero_mul_l (zero_mul_l (zero_mul_l s0 _) _) _).eqSymm)
  · let C : List (Fm PTm n) := (e ≐ succ (pred e)) :: Γ
    have hd : C ⊢[PRAAx] e ≐ succ (pred e) := Prf.hyp0
    have m1 := mu_bound hd (le_trans he.wk hkN.wk)
    have m2 := mu_bound hd he.wk
    have mP : C ⊢[PRAAx] muP (succ N) e ≐ muP (succ k) e := (Prf.andE₁ m1).eqTrans (Prf.andE₁ m2).eqSymm
    have mN : C ⊢[PRAAx] muN (succ N) e ≐ muN (succ k) e := (Prf.andE₂ m1).eqTrans (Prf.andE₂ m2).eqSymm
    exact .andI (a.wk.eqTrans ((congrMul (.eqRefl _) (congrMul mP (.eqRefl _))).eqTrans
        (by ipra_ring)))
      (b.wk.eqTrans ((congrMul (.eqRefl _) (congrMul mN (.eqRefl _))).eqTrans
        (by ipra_ring)))

theorem iv_rl {k N : PTm n} (hkN : Γ ⊢[PRAAx] le (succ k) (succ N)) :
    Γ ⊢[PRAAx] (ap2 (sumF (ivB (fP w))) (succ k) (pairT k N) ≐ ap2 (sumF (RLP w)) (succ k) k) ⋏
      (ap2 (sumF (ivB (fN w))) (succ k) (pairT k N) ≐ ap2 (sumF (RLN w)) (succ k) k) := by
  have hs : Syn.shift (succ k) = succ (Syn.shift k) := by simp [Syn.shift]
  have hkN' : Γ.map Fm.shift ⊢[PRAAx] le (succ (Syn.shift k)) (succ (Syn.shift N)) := by
    have e := hkN.shift
    simp only [Fm.shift, subst_le, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at e
    exact e
  have pt : (lt (var 0) (Syn.shift (succ k)) :: Γ.map Fm.shift) ⊢[PRAAx]
      (inst2 (ivB (fP w)) (var 0) (pairT (Syn.shift k) (Syn.shift N)) ≐ inst2 (RLP w) (var 0) (Syn.shift k)) ⋏
        (inst2 (ivB (fN w)) (var 0) (pairT (Syn.shift k) (Syn.shift N)) ≐ inst2 (RLN w) (var 0) (Syn.shift k)) := by
    rw [hs]
    exact rl_pt w (Prf.hyp0 : (lt (var 0) (succ (Syn.shift k)) :: Γ.map Fm.shift) ⊢[PRAAx] le (succ (var 0)) (succ (Syn.shift k))) hkN'.wk
  refine .andI (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))) (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_)))
  · rw [shift_pairT]; exact Prf.andE₁ pt
  · rw [shift_pairT]; exact Prf.andE₂ pt

/-- The inner sums of `μ⁻ L_w` and `μ⁺ L_w` differ by `Λ_w`: for `1 ≤ k ≤ N`,
`∑_{e ∣ k} μ⁻(e) L_w(e) = Λ_w(k) + ∑_{e ∣ k} μ⁺(e) L_w(e)`. -/
theorem key_inner {k N : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) (hkN : Γ ⊢[PRAAx] le (succ k) (succ N)) :
    Γ ⊢[PRAAx] ap2 (sumF (ivB (fN w))) (succ N) (pairT k N) ≐
      Lam w k zero + ap2 (sumF (ivB (fP w))) (succ N) (pairT k N) := by
  have cP := (iv_cut (fP w) hk hkN).eqTrans (Prf.andE₁ (iv_rl w hkN))
  have cN := (iv_cut (fN w) hk hkN).eqTrans (Prf.andE₂ (iv_rl w hkN))
  exact cN.eqTrans ((lambda_mobius_neg' w hk).eqSymm.eqTrans (congrAdd (.eqRefl _) cP.eqSymm))

/-! ## Rows of the two inversions -/

/-- `[d ∣ N] μ^±(d) Λ_w(N/d)`. -/
abbrev QAP : PTm 2 := PB * ap2 (sumF (lamB w)) (succ (quo (var 1) (var 0))) (pairT (quo (var 1) (var 0)) zero)
abbrev QAN : PTm 2 := NB * ap2 (sumF (lamB w)) (succ (quo (var 1) (var 0))) (pairT (quo (var 1) (var 0)) zero)

theorem inst2_QAP (d N : PTm n) :
    inst2 (QAP w) d N = ((sg d * eqb (rem N d) zero) * muP (succ N) d) * Lam w (quo N d) zero := by simp [inst2]
theorem inst2_QAN (d N : PTm n) :
    inst2 (QAN w) d N = ((sg d * eqb (rem N d) zero) * muN (succ N) d) * Lam w (quo N d) zero := by simp [inst2]

theorem row_gen (f : PTm 2) (d N : PTm n) :
    Γ ⊢[PRAAx] (inst2 (oB (aP f)) d (pairT (succ N) N) ≐
        ((sg d * eqb (rem N d) zero) * muP (succ N) d) * ap2 (sumF (ivB f)) (succ N) (pairT (quo N d) N)) ⋏
      (inst2 (oB (aN f)) d (pairT (succ N) N) ≐
        ((sg d * eqb (rem N d) zero) * muN (succ N) d) * ap2 (sumF (ivB f)) (succ N) (pairT (quo N d) N)) := by
  rw [inst2_oB, inst2_oB]
  have f₁ : Γ ⊢[PRAAx] fstT (pairT (succ N) N) ≐ succ N := fst_pair _ _
  have s₁ : Γ ⊢[PRAAx] sndT (pairT (succ N) N) ≐ N := snd_pair _ _
  have cR := congrAp2 (sumF (rowB (aP f))) f₁ (congrPairT (.eqRefl d) s₁)
  have cR' := congrAp2 (sumF (rowB (aN f))) f₁ (congrPairT (.eqRefl d) s₁)
  have hcP : Syn.shift ((sg d * eqb (rem N d) zero) * muP (succ N) d) =
      (sg (Syn.shift d) * eqb (rem (Syn.shift N) (Syn.shift d)) zero) * muP (succ (Syn.shift N)) (Syn.shift d) := by
    simp [Syn.shift]
  have hcN : Syn.shift ((sg d * eqb (rem N d) zero) * muN (succ N) d) =
      (sg (Syn.shift d) * eqb (rem (Syn.shift N) (Syn.shift d)) zero) * muN (succ (Syn.shift N)) (Syn.shift d) := by
    simp [Syn.shift]
  have hq : Syn.shift (quo N d) = quo (Syn.shift N) (Syn.shift d) := by simp [Syn.shift]
  have scP : Γ ⊢[PRAAx] ap2 (sumF (rowB (aP f))) (succ N) (pairT d N) ≐
      ((sg d * eqb (rem N d) zero) * muP (succ N) d) * ap2 (sumF (ivB f)) (succ N) (pairT (quo N d) N) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_rowB]
    simp only [shift_pairT]
    rw [hcP, hq]
    refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_aP]
    exact congrMul (.eqRefl _) (iv_at f _ _ _).eqSymm
  have scN : Γ ⊢[PRAAx] ap2 (sumF (rowB (aN f))) (succ N) (pairT d N) ≐
      ((sg d * eqb (rem N d) zero) * muN (succ N) d) * ap2 (sumF (ivB f)) (succ N) (pairT (quo N d) N) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_rowB]
    simp only [shift_pairT]
    rw [hcN, hq]
    refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_aN]
    exact congrMul (.eqRefl _) (iv_at f _ _ _).eqSymm
  exact .andI (cR.eqTrans scP) (cR'.eqTrans scN)

/-- The rows for `μ⁻ L_w` are those for `μ⁺ L_w` plus `[d ∣ N] μ^±(d) Λ_w(N/d)`. -/
theorem row_diff {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (d : PTm n) :
    Γ ⊢[PRAAx] (inst2 (oB (aP (fN w))) d (pairT (succ N) N) ≐
        inst2 (QAP w) d N + inst2 (oB (aP (fP w))) d (pairT (succ N) N)) ⋏
      (inst2 (oB (aN (fN w))) d (pairT (succ N) N) ≐
        inst2 (QAN w) d N + inst2 (oB (aN (fP w))) d (pairT (succ N) N)) := by
  have r1 := row_gen (Γ := Γ) (fN w) d N
  have r2 := row_gen (Γ := Γ) (fP w) d N
  rw [inst2_QAP, inst2_QAN]
  have key (X : PTm n) : Γ ⊢[PRAAx] ((sg d * eqb (rem N d) zero) * X) *
        ap2 (sumF (ivB (fN w))) (succ N) (pairT (quo N d) N) ≐
      ((sg d * eqb (rem N d) zero) * X) * Lam w (quo N d) zero +
        ((sg d * eqb (rem N d) zero) * X) * ap2 (sumF (ivB (fP w))) (succ N) (pairT (quo N d) N) :=
    (DivisorCases.divisor_quo_congr X hN fun hk hkN => key_inner w hk hkN).eqTrans (by ipra_ring)
  exact .andI ((Prf.andE₁ r1).eqTrans ((key _).eqTrans (congrAdd (.eqRefl _) (Prf.andE₁ r2).eqSymm)))
    ((Prf.andE₂ r1).eqTrans ((key _).eqTrans (congrAdd (.eqRefl _) (Prf.andE₂ r2).eqSymm)))

/-- `∑_{d ∣ N} μ(d) Λ_w(N/d) = −μ(N) L_w(N)` for `N ≥ 1`, as
`∑ μ⁺(d) Λ_w(N/d) + μ⁺(N) L_w(N) = ∑ μ⁻(d) Λ_w(N/d) + μ⁻(N) L_w(N)`. -/
theorem mu_lambda_conv {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] ap2 (sumF (QAP w)) (succ N) N + muP (succ N) N * Lw w N zero ≐
      ap2 (sumF (QAN w)) (succ N) N + muN (succ N) N * Lw w N zero := by
  have I₁ := mobius_inversion (Γ := Γ) (fN w) hN
  have I₂ := mobius_inversion (Γ := Γ) (fP w) hN
  rw [inst2_fN] at I₁
  rw [inst2_fP] at I₂
  have hN' := shift_pos hN
  have hs : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  have sP : Γ ⊢[PRAAx] ap2 (sumF (oB (aP (fN w)))) (succ N) (pairT (succ N) N) ≐
      ap2 (sumF (QAP w)) (succ N) N + ap2 (sumF (oB (aP (fP w)))) (succ N) (pairT (succ N) N) := by
    refine sum_add2 _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, hs]
    exact Prf.andE₁ (row_diff w hN'.wk _)
  have sN : Γ ⊢[PRAAx] ap2 (sumF (oB (aN (fN w)))) (succ N) (pairT (succ N) N) ≐
      ap2 (sumF (QAN w)) (succ N) N + ap2 (sumF (oB (aN (fP w)))) (succ N) (pairT (succ N) N) := by
    refine sum_add2 _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, hs]
    exact Prf.andE₂ (row_diff w hN'.wk _)
  ipra_lc -natEq sP + natEq sN + natEq I₁ - natEq I₂

/-- `μ^±_{N+1}(a) Λ_w(b)`, over `0 = a`, `1 = b`, `2 = N`. -/
abbrev mlamP : PTm 3 := muP (succ (var 2)) (var 0) * ap2 (sumF (lamB w)) (succ (var 1)) (pairT (var 1) zero)
abbrev mlamN : PTm 3 := muN (succ (var 2)) (var 0) * ap2 (sumF (lamB w)) (succ (var 1)) (pairT (var 1) zero)

theorem inst3_mlamP (a b N : PTm n) : inst3 (mlamP w) a b N = muP (succ N) a * Lam w b zero := by simp [inst3]
theorem inst3_mlamN (a b N : PTm n) : inst3 (mlamN w) a b N = muN (succ N) a * Lam w b zero := by simp [inst3]

/-- `thm:mu-lambda`: `∑_{d ∣ N} μ(N/d) Λ_w(d) = −μ(N) L_w(N)` for `N ≥ 1`, as
`∑_{d ∣ N} μ⁺(N/d) Λ_w(d) + μ⁺(N) L_w(N) = ∑_{d ∣ N} μ⁻(N/d) Λ_w(d) + μ⁻(N) L_w(N)`. -/
theorem mu_lambda {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] ap2 (sumF (DivisorSwap.TB (mlamP w))) (succ N) N + muP (succ N) N * Lw w N zero ≐
      ap2 (sumF (DivisorSwap.TB (mlamN w))) (succ N) N + muN (succ N) N * Lw w N zero := by
  have cP : Γ ⊢[PRAAx] ap2 (sumF (DivisorSwap.SB (mlamP w))) (succ N) N ≐ ap2 (sumF (QAP w)) (succ N) N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [DivisorSwap.inst2_SB, inst3_mlamP, inst2_QAP]
    ipra_ring
  have cN : Γ ⊢[PRAAx] ap2 (sumF (DivisorSwap.SB (mlamN w))) (succ N) N ≐ ap2 (sumF (QAN w)) (succ N) N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [DivisorSwap.inst2_SB, inst3_mlamN, inst2_QAN]
    ipra_ring
  ipra_lc -natEq (DivisorSwap.div_swap (mlamP w) hN) + natEq cP + natEq (mu_lambda_conv w hN) - natEq cN +
    natEq (DivisorSwap.div_swap (mlamN w) hN)

end MuLambda

end LeanProofs.IPRA.AnalyticNumberTheory.MuLambda
