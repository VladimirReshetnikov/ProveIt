import IPRADerivations.AnalyticNumberTheory.BlockTests
import IPRADerivations.AnalyticNumberTheory.ContractionMain
import IPRADerivations.Foundations.WindowStability

/-!
# The first two cases of the block deficit (`pnt_ipra_constructive_2026-11-14`, `con:deficit`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, proof of Lemma `con:deficit`:
"First suppose that `b_i < a/4` for all `0 ≤ i ≤ m/2` … `∫_s^{s+H/2} d(t) dt ≥ (aH/2 − 20)/3`." With a half-block of
harmonic length `S(D₂) − S(D_h) ≥ F H₀` and `16 D A H₀ ≥ 3A² + 384 D²` (`a = A/D`), the deficit `g = AQ ∸ D|P − Q|`
satisfies the uniform bound

  `3 A² F x ≤ 48 D Σ_{block} g + 16 A D F D₂`:

* `S_gap`: `S(b) ≥ S(a) + (b − a)⌊F/b⌋`; `mass_interior`: `(b − a) F⌊x/b⌋ ≤ Σ_{a<d≤b} F⌊x/d⌋ + F b`;
* `block_mono`: the deficit sum over a sub-block is at most the sum over the block;
* `case_A` (no high sample in the half `D_h < d ≤ D₂`, i.e. small `m`): `case_lo_sum` + `block_mean_lower`
  + `mass_lower`; `case_B` (no low sample in `D₁ < d ≤ D_h`): `case_hi_sum` + `block_mean_upper` + `mass_lower`.

The certificates are exact: `16D·(case) + 16D²·(mean) + 16DA·(mass) + 16DAx·(length) + Fx·(H₀)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.BlockCases

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB inst2_h quo_anti)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.SummatoryCompose (hRB)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockSums (biB pzB fzB block_mean_upper block_mean_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockMass (mass_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockDeficit (gzB gz_at term_at tw bv bv_in tw_cases OnBlock stg Pm Qm Bs'
  case_lo_sum case_hi_sum)
open LeanProofs.IPRA.AnalyticNumberTheory.ContractionMain (fq_le)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg)
open LeanProofs.IPRA.Foundations.WindowStability (sum_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHarmonic (shift_fact')
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Signum (sg sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `S(b) ≥ S(a) + (b − a)⌊F/b⌋` for `a ≤ b`. -/
theorem S_gap {a b : PTm n} (F : PTm n) (hab : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] le (monus b a * quo F b + S a F) (S b F) := by
  have hab' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift a) (Syn.shift b) := by simpa [Fm.shift, Syn.shift] using hab.shift
  have sp := natEq ((congrAp2 (Γ := Γ) (sumF hB) (eq_add_of_le hab) (.eqRefl F)).eqTrans (sum_split hB a (monus b a) F))
  have lo := sum_lower (Γ := Γ) (f := offB hB) (N := monus b a) (x := pairT a F) (m := quo F b) (.allI (.impI (by
    simp only [shift_pairT]
    rw [inst2_offB, inst2_h, show Syn.shift (quo F b) = quo (Syn.shift F) (Syn.shift b) by simp [Syn.shift]]
    have hv : (lt (var 0) (Syn.shift (monus b a)) :: Γ.map Fm.shift) ⊢[PRAAx]
        lt (var 0) (monus (Syn.shift b) (Syn.shift a)) := by
      have h0 : (lt (var 0) (Syn.shift (monus b a)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift (monus b a)) :=
        Prf.hyp0
      have e : Syn.shift (monus b a) = monus (Syn.shift b) (Syn.shift a) := by simp [Syn.shift]
      rw [e] at h0 ⊢; exact h0
    have e' := natEq (eq_add_of_le (hab'.wk (ψ := lt (var 0) (Syn.shift (monus b a)))))
    have hle : (lt (var 0) (Syn.shift (monus b a)) :: Γ.map Fm.shift) ⊢[PRAAx]
        le (succ (Syn.shift a + var 0)) (Syn.shift b) := by
      ipra_le sl hv with e'
    exact le_congr (.eqRefl _) (congrAp2 quoF (snd_pair _ _).eqSymm
        (congrSucc (congrAdd (fst_pair _ _) (.eqRefl _))).eqSymm)
      (quo_anti (congrSucc (pred_succ _).eqSymm) hle))))
  ipra_le sl lo with sp

/-- `(b − a) F⌊x/b⌋ ≤ Σ_{a<d≤b} F⌊x/d⌋ + F b` for `1 ≤ b ≤ min(x, L)`. -/
theorem mass_interior {x a b K L w : PTm n} (hab : Γ ⊢[PRAAx] le a b) (hbx : Γ ⊢[PRAAx] le b x)
    (hbL : Γ ⊢[PRAAx] le b L) (hb1 : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] le (monus b a * (fact L * quo x b))
      (ap2 (sumF (hRB fzB biB)) (succ x) (pairT x (BlockSums.Y a b w (pairT K (fact L)))) + fact L * b) := by
  have ms := mass_lower (w := w) (K := K) hab hbx hbL
  have sg := S_gap (fact L) hab
  have fq := le_scale (monus b a) (fq_le (x := x) (pos_of_one_le hb1) hbL)
  have sgx := le_scale x sg
  ipra_le sl fq + sl sgx + sl ms

/-- The deficit sum over a sub-block is at most the sum over the block. -/
theorem block_mono {x D₁ D₂ E₁ E₂ A Ds K L : PTm n} (h1 : Γ ⊢[PRAAx] le D₁ E₁) (h2 : Γ ⊢[PRAAx] le E₂ D₂)
    (hE : Γ ⊢[PRAAx] le E₁ E₂) :
    Γ ⊢[PRAAx] le (Bs' gzB x E₁ E₂ A Ds K L) (Bs' gzB x D₁ D₂ A Ds K L) := by
  have h1' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift D₁) (Syn.shift E₁) := by simpa [Fm.shift, Syn.shift] using h1.shift
  have h2' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift E₂) (Syn.shift D₂) := by simpa [Fm.shift, Syn.shift] using h2.shift
  have hE' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift E₁) (Syn.shift E₂) := by simpa [Fm.shift, Syn.shift] using hE.shift
  refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT, shift_fact']
  refine le_congr (term_at _ _ _ _ _ _ _).eqSymm (term_at _ _ _ _ _ _ _).eqSymm ?_
  refine le_congr (congrMul (.eqRefl _) (gz_at _ _ _ _ _ _ _)).eqSymm (congrMul (.eqRefl _) (gz_at _ _ _ _ _ _ _)).eqSymm ?_
  refine tw_cases (d := var 0) hE'.wk _ ?_ ?_
  · exact le_congr (zero_mul_l' Prf.hyp0 _).eqSymm (.eqRefl _) (zero_le _)
  · have hlt : ((tw (var 0) (Syn.shift E₁) (Syn.shift E₂) ≐ one) :: le (var 0) (Syn.shift E₂) ::
        lt (Syn.shift E₁) (var 0) :: lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx]
        lt (Syn.shift E₁) (var 0) := .hyp (by simp)
    have hle : ((tw (var 0) (Syn.shift E₁) (Syn.shift E₂) ≐ one) :: le (var 0) (Syn.shift E₂) ::
        lt (Syn.shift E₁) (var 0) :: lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx]
        le (var 0) (Syn.shift E₂) := .hyp (by simp)
    have hd : ((tw (var 0) (Syn.shift E₁) (Syn.shift E₂) ≐ one) :: le (var 0) (Syn.shift E₂) ::
        lt (Syn.shift E₁) (var 0) :: lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx]
        var 0 ≐ succ (pred (var 0)) :=
      pos_of_one_le (le_trans ((succ_monus_succ zero (Syn.shift E₁)).eqTrans (zero_le _)) hlt)
    have o := bv_in (lt_of_le_of_lt h1'.wk.wk.wk.wk hlt) (le_trans hle h2'.wk.wk.wk.wk)
    have t : ((tw (var 0) (Syn.shift E₁) (Syn.shift E₂) ≐ one) :: le (var 0) (Syn.shift E₂) ::
        lt (Syn.shift E₁) (var 0) :: lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx]
        tw (var 0) (Syn.shift D₁) (Syn.shift D₂) ≐ one :=
      (congrMul ((congrSg hd).eqTrans (sg_succ _)) o).eqTrans (by apply deriveNat; ipra_simps; ring)
    exact le_congr (congrMul Prf.hyp0 (.eqRefl _)).eqSymm (congrMul t (.eqRefl _)).eqSymm (le_refl _)
where
  zero_mul_l' {Δ : List (Fm PTm (n + 1))} {a : PTm (n + 1)} (h : Δ ⊢[PRAAx] a ≐ zero) (b : PTm (n + 1)) :
      Δ ⊢[PRAAx] a * b ≐ zero :=
    (congrMul h (.eqRefl _)).eqTrans (by apply deriveNat; ipra_simps; ring)

section Halves

variable {x D₁ Dh D₂ A Ds K L H0 : PTm n}

/-- Case A: no high sample on `D_h < d ≤ D₂`. -/
theorem case_A (h1 : Γ ⊢[PRAAx] le one Dh) (hh2 : Γ ⊢[PRAAx] le Dh D₂) (h2x : Γ ⊢[PRAAx] le D₂ x)
    (h2L : Γ ⊢[PRAAx] le D₂ L) (hK1 : Γ ⊢[PRAAx] le one K)
    (hPK : Γ ⊢[PRAAx] le (quo x Dh) K) (hPK' : Γ ⊢[PRAAx] le (quo x D₂) K)
    (hNN : Γ ⊢[PRAAx] le (K * pw (quo x Dh) (quo x Dh)) L) (hNN' : Γ ⊢[PRAAx] le (K * pw (quo x D₂) (quo x D₂)) L)
    (hKx : Γ ⊢[PRAAx] le (K * x) L) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)
    (hS : Γ ⊢[PRAAx] le (S Dh (fact L) + fact L * H0) (S D₂ (fact L)))
    (hH0 : Γ ⊢[PRAAx] le (num 3 * (A * A) + num 384 * (Ds * Ds)) (num 16 * (Ds * (A * H0))))
    (hb : Γ ⊢[PRAAx] OnBlock x Dh D₂ (stg x A Ds K L ⋏
      le (two * (Syn.shift Ds * monus (Pm x K L) (Qm x L))) (Syn.shift A * Qm x L))) :
    Γ ⊢[PRAAx] le (num 3 * (A * (A * (fact L * x))))
      (num 48 * (Ds * Bs' gzB x Dh D₂ A Ds K L) + num 16 * (A * (Ds * (fact L * D₂)))) := by
  have c := case_lo_sum hh2 hb
  have m := block_mean_lower (w := pairT A Ds) h1 hh2 h2x hK1 hPK hPK' hNN hNN' hKx hP
  have ms := mass_lower (w := pairT A Ds) (K := K) hh2 h2x h2L
  ipra_le 16 * 𝔞 Ds * sl c + 16 * 𝔞 Ds * 𝔞 Ds * sl m + 16 * 𝔞 Ds * 𝔞 A * sl ms +
    16 * 𝔞 Ds * 𝔞 A * 𝔞 x * sl hS + 𝔞 (fact L) * 𝔞 x * sl hH0

/-- Case B: no low sample on `D₁ < d ≤ D_h`. -/
theorem case_B (h1 : Γ ⊢[PRAAx] le one D₁) (h1h : Γ ⊢[PRAAx] le D₁ Dh) (hhx : Γ ⊢[PRAAx] le Dh x)
    (hhL : Γ ⊢[PRAAx] le Dh L) (hK1 : Γ ⊢[PRAAx] le one K)
    (hPK : Γ ⊢[PRAAx] le (quo x D₁) K) (hPK' : Γ ⊢[PRAAx] le (quo x Dh) K)
    (hNN : Γ ⊢[PRAAx] le (K * pw (quo x D₁) (quo x D₁)) L) (hNN' : Γ ⊢[PRAAx] le (K * pw (quo x Dh) (quo x Dh)) L)
    (hKx : Γ ⊢[PRAAx] le (K * x) L) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)
    (hS : Γ ⊢[PRAAx] le (S D₁ (fact L) + fact L * H0) (S Dh (fact L)))
    (hH0 : Γ ⊢[PRAAx] le (num 3 * (A * A) + num 384 * (Ds * Ds)) (num 16 * (Ds * (A * H0))))
    (hb : Γ ⊢[PRAAx] OnBlock x D₁ Dh (stg x A Ds K L ⋏
      le (two * (Syn.shift Ds * monus (Qm x L) (Pm x K L))) (Syn.shift A * Qm x L))) :
    Γ ⊢[PRAAx] le (num 3 * (A * (A * (fact L * x))))
      (num 48 * (Ds * Bs' gzB x D₁ Dh A Ds K L) + num 16 * (A * (Ds * (fact L * Dh)))) := by
  have c := case_hi_sum h1h hb
  have m := block_mean_upper (w := pairT A Ds) h1 h1h hhx hK1 hPK hPK' hNN hNN' hKx hP
  have ms := mass_lower (w := pairT A Ds) (K := K) h1h hhx hhL
  ipra_le 16 * 𝔞 Ds * sl c + 16 * 𝔞 Ds * 𝔞 Ds * sl m + 16 * 𝔞 Ds * 𝔞 A * sl ms +
    16 * 𝔞 Ds * 𝔞 A * 𝔞 x * sl hS + 𝔞 (fact L) * 𝔞 x * sl hH0

end Halves

end LeanProofs.IPRA.AnalyticNumberTheory.BlockCases
