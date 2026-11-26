import IPRADerivations.AnalyticNumberTheory.HarmonicChebyshev
import IPRADerivations.AnalyticNumberTheory.HarmonicLambda
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# Subadditivity of the harmonic logarithm and Mertens' upper bound (`pnt_ipra_constructive_2026-11-14`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, Lemma `sb:basic-psi`,
inequality `sb:mertens-bound` (`|∑_{n≤x} Λ(n)/n − log x| ≤ 6`), which feeds `sb:signed-integral` and
hence the contraction hypothesis `con:signed`. Everything is stated for the packet's rational logarithm
`λ_M(a) = H_{Ma} − H_M` (common denominator `F = L!`), with no passage to real limits:

* `subadd`: `λ_M(ab) ≤ λ_M(a) + λ_M(b) + 1/M` — the second conjunct of `LogRefinement.log_refine`
  (the finite error form of logarithm additivity of `sec:log`);
* `pow_sub`: `λ_M(a^K) ≤ K λ_M(a) + K/M`, one QF induction on the exponent;
* `mertens_upper` (`sb:mertens-bound`, upper half): with the weight `Λ_w(p^a) = λ_M(p)` of
  `HarmonicChebyshev`, `∑_{d ≤ N} Λ_w(d) ⌊N!/d⌋ + N! S(M) ≤ N! (S(MN) + ⌊F/M⌋ + 4F)`, i.e.
  `∑_{d≤N} Λ(d)/d ≤ λ_M(N) + 4 + 1/M` (the packet's `≤ log N + 6`), from `HarmonicLambda.harmonic_sandwich`,
  `HarmonicChebyshev.harmonic_lw`, `N! ≤ N^N`, `pow_sub` and `HarmonicChebyshev.psi_le`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB inst2_h)
open LeanProofs.IPRA.AnalyticNumberTheory.LogRefinement (log_refine)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono wt harmonic_lw psi_le)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLambda (Sw harmonic_sandwich fact_le_pow)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (Lw)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (Psi pos_of_lt_zero lt_zero_of_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open LeanProofs.IPRA.Analysis.Products (fact)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `a ≤ b → c a ≤ c b`. -/
theorem le_scale (c : PTm n) {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (c * a) (c * b) := by
  refine le_of_eq_add (d := c * monus b a) ?_
  ipra_lc 𝔞 c * natEq (eq_add_of_le h)

/-- Subadditivity with error: `λ_M(ab) ≤ λ_M(a) + λ_M(b) + 1/M`, i.e.
`S(Mab) + S(M) ≤ S(Ma) + S(Mb) + ⌊F/M⌋` at the mesh `F = L!`, `Mab ≤ L`. -/
theorem subadd {M a b L : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) (hL : Γ ⊢[PRAAx] le (M * (a * b)) L) :
    Γ ⊢[PRAAx] le (S (M * (a * b)) (fact L) + S M (fact L))
      (S (M * a) (fact L) + S (M * b) (fact L) + quo (fact L) M) := by
  have wM := natEq hM; have wb := natEq hb
  have q1 : Γ ⊢[PRAAx] M * (a * b) ≐ a * (succ (pred M) + M * pred b) := by
    ipra_lc 𝔞 a * wM + 𝔞 a * 𝔞 M * wb
  have hL' : Γ ⊢[PRAAx] le (a * (succ (pred M) + M * pred b)) L := le_congr q1 (.eqRefl _) hL
  have r := Prf.andE₂ (log_refine (c₁ := pred M) (T := M * pred b) ha hL')
  have q3 : Γ ⊢[PRAAx] M * a ≐ a * succ (pred M) := by
    ipra_lc 𝔞 a * wM
  have q4 : Γ ⊢[PRAAx] M * b ≐ succ (pred M + M * pred b) := by
    ipra_lc wM + 𝔞 M * wb
  have fab := natEq (congrAp2 (Γ := Γ) (sumF hB) q1 (.eqRefl (fact L)))
  have fa := natEq (congrAp2 (Γ := Γ) (sumF hB) q3 (.eqRefl (fact L)))
  have sM : Γ ⊢[PRAAx] S M (fact L) ≐ S (pred M) (fact L) + quo (fact L) (succ (pred M)) := by
    refine (congrAp2 (sumF hB) hM (.eqRefl _)).eqTrans ?_
    have s := sum_succ' (Γ := Γ) hB (pred M) (fact L)
    rw [inst2_h] at s
    exact s
  have fM := natEq sM
  have sMb : Γ ⊢[PRAAx] S (M * b) (fact L) ≐
      S (pred M + M * pred b) (fact L) + quo (fact L) (succ (pred M + M * pred b)) := by
    refine (congrAp2 (sumF hB) q4 (.eqRefl _)).eqTrans ?_
    have s := sum_succ' (Γ := Γ) hB (pred M + M * pred b) (fact L)
    rw [inst2_h] at s
    exact s
  have fb := natEq sMb
  have fq := natEq (congrAp2 (Γ := Γ) quoF (.eqRefl (fact L)) hM)
  ipra_le sl r + 𝔞 (quo (fact L) (succ (pred M + M * pred b))) with fab + fM - fa - fb - fq

/-! ## Powers -/

/-- `λ_M(a^k) ≤ k λ_M(a) + k/M`. -/
abbrev P (k a M L : PTm n) : Fm PTm n :=
  le (S (M * pw a k) (fact L) + k * S M (fact L))
    (S M (fact L) + k * S (M * a) (fact L) + k * quo (fact L) M)

abbrev Hp (k a M L K : PTm n) : Fm PTm n :=
  le one M ⋏ (le one a ⋏ (le (M * pw a K) L ⋏ le k K))

theorem p_zero (a M L : PTm n) : Γ ⊢[PRAAx] P zero a M L := by
  have q : Γ ⊢[PRAAx] M * pw a zero ≐ M := by
    ipra_lc 𝔞 M * natEq (pw_zero (Γ := Γ) a)
  have e0 := natEq (congrAp2 (Γ := Γ) (sumF hB) q (.eqRefl (fact L)))
  ipra_le 0 with e0

theorem p_step {k a M L K : PTm n} (h : Γ ⊢[PRAAx] Hp (succ k) a M L K) (ih : Γ ⊢[PRAAx] P k a M L) :
    Γ ⊢[PRAAx] P (succ k) a M L := by
  have hM := pos_of_lt_zero (Prf.andE₁ h)
  have ha := pos_of_lt_zero (Prf.andE₁ (Prf.andE₂ h))
  have hK := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have hk := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))
  have mono := le_scale M (pw_le_exp ha hk)
  have q : Γ ⊢[PRAAx] M * pw a (succ k) ≐ M * (pw a k * a) := by
    ipra_lc 𝔞 M * natEq (pw_succ (Γ := Γ) a k)
  have hL : Γ ⊢[PRAAx] le (M * (pw a k * a)) L := le_trans (le_congr q (.eqRefl _) mono) hK
  have sub := subadd hM (pw_pos' ha k) ha hL
  have e := natEq (congrAp2 (Γ := Γ) (sumF hB) q (.eqRefl (fact L)))
  ipra_le sl ih + sl sub with e

/-- Variables: `0 = k`, `1 = a`, `2 = M`, `3 = L`, `4 = K`. -/
private abbrev powF : Fm PTm 5 :=
  Hp (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ P (var 0) (var 1) (var 2) (var 3)

private theorem pow₀ : ([] : List (Fm PTm 5)) ⊢[PRAAx] powF := by
  ipra_ind (⟨⟨le_QF _ _, le_QF _ _, le_QF _ _, le_QF _ _⟩, le_QF _ _⟩) [subst_le, subst_ap2]
  · exact .impI (p_zero _ _ _)
  · refine .impI ?_
    have h := (Prf.hyp0 : (Hp (succ (var 0)) (var 1) (var 2) (var 3) (var 4) :: [powF]) ⊢[PRAAx]
      Hp (succ (var 0)) (var 1) (var 2) (var 3) (var 4))
    have h' : (Hp (succ (var 0)) (var 1) (var 2) (var 3) (var 4) :: [powF]) ⊢[PRAAx]
        Hp (var 0) (var 1) (var 2) (var 3) (var 4) :=
      .andI (Prf.andE₁ h) (.andI (Prf.andE₁ (Prf.andE₂ h)) (.andI (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h)))
        (le_trans (le_succ_self _) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))))))
    exact p_step h (Prf.impE Prf.hyp1 h')

/-- `λ_M(a^K) ≤ K λ_M(a) + K/M`: `S(M a^K) + K S(M) ≤ S(M) + K S(Ma) + K ⌊F/M⌋` for `M, a ≥ 1`, `M a^K ≤ L`. -/
theorem pow_sub {a M L K : PTm n} (hM : Γ ⊢[PRAAx] le one M) (ha : Γ ⊢[PRAAx] le one a)
    (hL : Γ ⊢[PRAAx] le (M * pw a K) L) : Γ ⊢[PRAAx] P K a M L := by
  have i := inst (Γ := Γ) pow₀ (![K, a, M, L, K] : Fin 5 → PTm n)
  simp at i
  exact Prf.impE i (.andI hM (.andI ha (.andI hL (le_refl K))))

/-! ## Mertens' upper bound -/

/-- `sb:mertens-bound`, upper half, for the harmonic logarithm:
`∑_{d ≤ N} Λ_w(d) ⌊N!/d⌋ + N! S(M) ≤ N! (S(MN) + ⌊F/M⌋ + 4F)`, i.e.
`∑_{d≤N} Λ(d)/d ≤ λ_M(N) + 4 + 1/M`, for `N, M ≥ 1`, `M N^N ≤ L`, `M 2^{4N} ≤ L`, `F = L!`. -/
theorem mertens_upper {N M L : PTm n} (hN : Γ ⊢[PRAAx] le one N) (hM : Γ ⊢[PRAAx] le one M)
    (hNN : Γ ⊢[PRAAx] le (M * pw N N) L) (h2 : Γ ⊢[PRAAx] le (M * pw two (two * (two * N))) L) :
    Γ ⊢[PRAAx] le (Sw wt N (pairT M (fact L)) + fact N * S M (fact L))
      (fact N * (S (M * N) (fact L) + quo (fact L) M + two * (two * fact L))) := by
  have sw := Prf.andE₂ (harmonic_sandwich (Γ := Γ) wt N (pairT M (fact L)))
  have mf := le_scale M (fact_le_pow (Γ := Γ) N)
  have hl := le_scale (fact N) (harmonic_lw (lt_zero_of_pos (Primes.fact_pos N)) hM (le_trans mf hNN))
  have sm := le_scale (fact N) (S_mono (fact L) mf)
  have pw' := le_scale (fact N) (pow_sub hM hN hNN)
  have ps := le_scale (fact N) (psi_le hM h2)
  have hNp := pos_of_lt_zero hN
  refine mul_le_cancel (d' := pred N) ?_
  have c : Γ ⊢[PRAAx] le (N * (Sw wt N (pairT M (fact L)) + fact N * S M (fact L)))
      (N * (fact N * (S (M * N) (fact L) + quo (fact L) M + two * (two * fact L)))) := by
    ipra_le sl sw + sl hl + sl sm + sl pw' + sl ps
  exact le_congr (congrMul hNp (.eqRefl _)) (congrMul hNp (.eqRefl _)) c

end LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens
