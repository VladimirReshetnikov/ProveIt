import IPRADerivations.AnalyticNumberTheory.HarmonicMertens
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.InductionTactic

/-!
# Mertens' lower bound for the harmonic logarithm (`pnt_ipra_constructive_2026-11-14`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, Lemma `sb:basic-psi`,
inequality `sb:mertens-bound` (`|∑_{n≤x} Λ(n)/n − log x| ≤ 6`), lower half; with
`HarmonicMertens.mertens_upper` this closes `sb:mertens-bound` for the packet's rational logarithm
`λ_M(a) = H_{Ma} − H_M` (common denominator `F = L!`), the input of `sb:signed-integral`/`con:signed`.

* `lw_lower`: `λ_M(m) ≤ L_w(m) + m/M` — one QF induction along the least-prime-factor trace with the
  invariant `S(Mm) + L_w(x_i) ≤ S(M x_i) + L_w(m) + i⌊F/M⌋` (each prime step is `HarmonicMertens.subadd`);
* `delta_le`: `n (λ_M(n+1) − λ_M(n)) ≤ 1`, from `LogElementary.log_upper` after cancelling `M`;
* `fact_lower`: `n λ_M(n) ≤ L_w(n!) + n + n²/M`, one QF induction on `n` (`L_w((n+1)!) = L_w(n!) + L_w(n+1)`);
* `mertens_lower`: `N! S(MN) ≤ ∑_{d≤N} Λ_w(d)⌊N!/d⌋ + N! (S(M) + F + N⌊F/M⌋)`, i.e.
  `∑_{d≤N} Λ(d)/d ≥ λ_M(N) − 1 − N/M` (`≥ λ_M(N) − 2` for `M ≥ N`), from the first half of
  `HarmonicLambda.harmonic_sandwich`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertensLower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.LogElementary (log_upper)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono wt lw_prime tr_pos tr_le Hy)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (subadd le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLambda (Sw harmonic_sandwich)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorTrace (trT tr_zero tr_succ step_small trace_prime trace_end lpf_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (lpf prime)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (Lw)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (congrLw lw_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (pos_of_lt_zero lt_zero_of_pos)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## `λ_M(m) ≤ L_w(m) + m/M` along the trace -/

/-- The invariant `S(Mm) + L_w(x_i) ≤ S(M x_i) + L_w(m) + i ⌊F/M⌋`. -/
abbrev K (m M L i : PTm n) : Fm PTm n :=
  le (S (M * m) (fact L) + Lw wt (trT i m) (pairT M (fact L)))
    (S (M * trT i m) (fact L) + Lw wt m (pairT M (fact L)) + i * quo (fact L) M)

theorem k_zero (m M L : PTm n) : Γ ⊢[PRAAx] K m M L zero := by
  have t0 := tr_zero (Γ := Γ) m
  have eS := natEq (congrAp2 (Γ := Γ) (sumF hB) (congrMul (.eqRefl M) t0) (.eqRefl (fact L)))
  have eL := natEq (congrLw (Γ := Γ) (w := wt) (pairT M (fact L)) t0)
  ipra_le 0 with eL - eS

theorem k_step {m M L i : PTm n} (hm : Γ ⊢[PRAAx] le one m) (hM : Γ ⊢[PRAAx] le one M)
    (hL : Γ ⊢[PRAAx] le (M * m) L) (ih : Γ ⊢[PRAAx] K m M L i) : Γ ⊢[PRAAx] K m M L (succ i) := by
  have hx1 := tr_pos hm i
  have hxm := tr_le hm i
  refine .orE (lt_or_le one (trT i m)) ?_ ?_
  · let Δ := lt one (trT i m) :: Γ
    have hx2 : Δ ⊢[PRAAx] le two (trT i m) := Prf.hyp0
    have tp := trace_prime hx2
    have hp := Prf.andE₁ tp
    have ex := Prf.andE₂ tp
    have hx'p := pos_of_lt_zero (tr_pos (Γ := Δ) hm.wk (succ i))
    have hpp : Δ ⊢[PRAAx] lpf (trT i m) ≐ succ (pred (lpf (trT i m))) := lpf_pos _
    have hMp := pos_of_lt_zero (Γ := Δ) hM.wk
    have hL' : Δ ⊢[PRAAx] le (M * (lpf (trT i m) * trT (succ i) m)) L := by
      refine le_trans (le_of_eq_add (d := M * monus m (trT i m)) ?_) hL.wk
      ipra_lc 𝔞 M * natEq (eq_add_of_le (Γ := Δ) hxm.wk) - 𝔞 M * natEq ex
    have sub := subadd hMp hpp hx'p hL'
    have q1 : Δ ⊢[PRAAx] M * (lpf (trT i m) * trT (succ i) m) ≐ M * trT i m := by
      ipra_lc 𝔞 M * natEq ex
    have e1 := natEq (congrAp2 (Γ := Δ) (sumF hB) q1 (.eqRefl (fact L)))
    have hmono : Δ ⊢[PRAAx] le M (M * lpf (trT i m)) := by
      refine le_of_eq_add (d := M * pred (lpf (trT i m))) ?_
      ipra_lc 𝔞 M * natEq hpp
    have dec := natEq (eq_add_of_le (S_mono (fact L) hmono))
    have sp : Δ ⊢[PRAAx] Lw wt (trT i m) (pairT M (fact L)) ≐
        monus (S (M * lpf (trT i m)) (fact L)) (S M (fact L)) + Lw wt (trT (succ i) m) (pairT M (fact L)) :=
      (congrLw (w := wt) _ (ex.eqSymm.eqTrans (mul_comm _ _))).eqTrans
        ((lw_mul (w := wt) hpp hx'p).eqTrans (congrAdd (lw_prime M (fact L) hp) (.eqRefl _)))
    have e3 := natEq sp
    ipra_le sl ih.wk + sl sub with dec - e1 - e3
  · let Δ := le (trT i m) one :: Γ
    have xo : Δ ⊢[PRAAx] trT i m ≐ one := le_antisymm Prf.hyp0 hx1.wk
    have sx : Δ ⊢[PRAAx] trT (succ i) m ≐ one := (tr_succ i m).eqTrans (step_small Prf.hyp0)
    have exx := sx.eqTrans xo.eqSymm
    have eS := natEq (congrAp2 (Γ := Δ) (sumF hB) (congrMul (.eqRefl M) exx) (.eqRefl (fact L)))
    have eL := natEq (congrLw (Γ := Δ) (w := wt) (pairT M (fact L)) exx)
    ipra_le sl ih.wk + 𝔞 (quo (fact L) M) with eL - eS

/-- Variables: `0 = i`, `1 = m`, `2 = M`, `3 = L`. -/
private abbrev lowF : Fm PTm 4 := Hy (var 1) (var 2) (var 3) ⟶ K (var 1) (var 2) (var 3) (var 0)

private theorem low₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] lowF := by
  ipra_ind (⟨⟨le_QF _ _, le_QF _ _, le_QF _ _⟩, le_QF _ _⟩) [subst_le, subst_ap2, subst_pairT]
  · exact .impI (k_zero _ _ _)
  · refine .impI ?_
    have h := (Prf.hyp0 : (Hy (var 1) (var 2) (var 3) :: [lowF]) ⊢[PRAAx] Hy (var 1) (var 2) (var 3))
    exact k_step (Prf.andE₁ h) (Prf.andE₁ (Prf.andE₂ h)) (Prf.andE₂ (Prf.andE₂ h)) (Prf.impE Prf.hyp1 Prf.hyp0)

/-- `λ_M(m) ≤ L_w(m) + m/M`: `S(Mm) ≤ S(M) + L_w(m) + m ⌊F/M⌋` for `1 ≤ m`, `1 ≤ M`, `Mm ≤ L`. -/
theorem lw_lower {m M L : PTm n} (hm : Γ ⊢[PRAAx] le one m) (hM : Γ ⊢[PRAAx] le one M)
    (hL : Γ ⊢[PRAAx] le (M * m) L) :
    Γ ⊢[PRAAx] le (S (M * m) (fact L)) (S M (fact L) + Lw wt m (pairT M (fact L)) + m * quo (fact L) M) := by
  have i := inst (Γ := Γ) low₀ (![m, m, M, L] : Fin 4 → PTm n)
  simp at i
  have I : Γ ⊢[PRAAx] K m M L m := Prf.impE i (.andI hm (.andI hM hL))
  have te := trace_end (pos_of_lt_zero hm)
  have q : Γ ⊢[PRAAx] M * trT m m ≐ M := (congrMul (.eqRefl M) te).eqTrans (by ipra_ring)
  have eS := natEq (congrAp2 (Γ := Γ) (sumF hB) q (.eqRefl (fact L)))
  have eL := natEq ((congrLw (w := wt) (pairT M (fact L)) te).eqTrans (MuLambda.lw_one (w := wt) _))
  ipra_le sl I with eS - eL

/-! ## The increments and the factorial -/

/-- `n (λ_M(n+1) − λ_M(n)) ≤ 1`: `n S(M(n+1)) ≤ n S(Mn) + F`. -/
theorem delta_le {M : PTm n} (nn F : PTm n) (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) :
    Γ ⊢[PRAAx] le (nn * S (M * succ nn) F) (nn * S (M * nn) F + F) := by
  have lu := log_upper (Γ := Γ) (M * nn) M F
  have q : Γ ⊢[PRAAx] M * succ nn ≐ M * nn + M := by ipra_ring
  have e := natEq (congrAp2 (Γ := Γ) (sumF hB) q (.eqRefl F))
  have mono := S_mono (Γ := Γ) F (le_of_eq_add q : Γ ⊢[PRAAx] le (M * nn) (M * succ nn))
  refine mul_le_cancel (d' := pred M) ?_
  have c : Γ ⊢[PRAAx] le (M * (nn * S (M * succ nn) F)) (M * (nn * S (M * nn) F + F)) := by
    ipra_le sl lu + sl mono with (𝔞 M * 𝔞 nn + 1) * e
  exact le_congr (congrMul hM (.eqRefl _)) (congrMul hM (.eqRefl _)) c

/-- `n λ_M(n) ≤ L_w(n!) + n + n²/M`. -/
abbrev T (k M L : PTm n) : Fm PTm n :=
  le (k * S (M * k) (fact L))
    (k * S M (fact L) + Lw wt (fact k) (pairT M (fact L)) + k * fact L + k * k * quo (fact L) M)

abbrev Hf (k M L N : PTm n) : Fm PTm n := le one M ⋏ (le (M * N) L ⋏ le k N)

theorem t_zero (M L : PTm n) : Γ ⊢[PRAAx] T zero M L := by
  ipra_le 𝔞 (Lw wt (fact zero) (pairT M (fact L)))

theorem t_step {k M L N : PTm n} (h : Γ ⊢[PRAAx] Hf (succ k) M L N) (ih : Γ ⊢[PRAAx] T k M L) :
    Γ ⊢[PRAAx] T (succ k) M L := by
  have hM := Prf.andE₁ h
  have hL := Prf.andE₁ (Prf.andE₂ h)
  have hk := Prf.andE₂ (Prf.andE₂ h)
  have hMp := pos_of_lt_zero hM
  have hs : Γ ⊢[PRAAx] succ k ≐ succ (pred (succ k)) := congrSucc (pred_succ _).eqSymm
  have dl := delta_le (Γ := Γ) k (fact L) hMp
  have ll := lw_lower (lt_zero_of_pos hs) hM (le_trans (le_scale M hk) hL)
  have lf : Γ ⊢[PRAAx] Lw wt (fact (succ k)) (pairT M (fact L)) ≐
      Lw wt (fact k) (pairT M (fact L)) + Lw wt (succ k) (pairT M (fact L)) :=
    (congrLw (w := wt) _ (fact_succ k zero)).eqTrans (lw_mul (w := wt) (Primes.fact_pos k) hs)
  have e := natEq lf
  ipra_le sl ih + sl dl + sl ll + 𝔞 k * 𝔞 (quo (fact L) M) with -e

/-- Variables: `0 = k`, `1 = M`, `2 = L`, `3 = N`. -/
private abbrev factF' : Fm PTm 4 := Hf (var 0) (var 1) (var 2) (var 3) ⟶ T (var 0) (var 1) (var 2)

private theorem fact₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] factF' := by
  ipra_ind (⟨⟨le_QF _ _, le_QF _ _, le_QF _ _⟩, le_QF _ _⟩) [subst_le, subst_ap2, subst_pairT]
  · exact .impI (t_zero _ _)
  · refine .impI ?_
    have h := (Prf.hyp0 : (Hf (succ (var 0)) (var 1) (var 2) (var 3) :: [factF']) ⊢[PRAAx]
      Hf (succ (var 0)) (var 1) (var 2) (var 3))
    have h' : (Hf (succ (var 0)) (var 1) (var 2) (var 3) :: [factF']) ⊢[PRAAx] Hf (var 0) (var 1) (var 2) (var 3) :=
      .andI (Prf.andE₁ h) (.andI (Prf.andE₁ (Prf.andE₂ h)) (le_trans (le_succ_self _) (Prf.andE₂ (Prf.andE₂ h))))
    exact t_step h (Prf.impE Prf.hyp1 h')

/-- `N λ_M(N) ≤ L_w(N!) + N + N²/M` for `M ≥ 1`, `MN ≤ L`. -/
theorem fact_lower {N M L : PTm n} (hM : Γ ⊢[PRAAx] le one M) (hL : Γ ⊢[PRAAx] le (M * N) L) :
    Γ ⊢[PRAAx] T N M L := by
  have i := inst (Γ := Γ) fact₀ (![N, M, L, N] : Fin 4 → PTm n)
  simp at i
  exact Prf.impE i (.andI hM (.andI hL (le_refl N)))

/-! ## Mertens' lower bound -/

/-- `sb:mertens-bound`, lower half, for the harmonic logarithm:
`N! S(MN) ≤ ∑_{d≤N} Λ_w(d) ⌊N!/d⌋ + N! (S(M) + F + N ⌊F/M⌋)`, i.e.
`∑_{d≤N} Λ(d)/d ≥ λ_M(N) − 1 − N/M`, for `N, M ≥ 1`, `MN ≤ L`, `F = L!`. -/
theorem mertens_lower {N M L : PTm n} (hN : Γ ⊢[PRAAx] le one N) (hM : Γ ⊢[PRAAx] le one M)
    (hL : Γ ⊢[PRAAx] le (M * N) L) :
    Γ ⊢[PRAAx] le (fact N * S (M * N) (fact L))
      (Sw wt N (pairT M (fact L)) + fact N * (S M (fact L) + fact L + N * quo (fact L) M)) := by
  have sw := Prf.andE₁ (harmonic_sandwich (Γ := Γ) wt N (pairT M (fact L)))
  have t := le_scale (fact N) (fact_lower hM hL)
  have hNp := pos_of_lt_zero hN
  refine mul_le_cancel (d' := pred N) ?_
  have c : Γ ⊢[PRAAx] le (N * (fact N * S (M * N) (fact L)))
      (N * (Sw wt N (pairT M (fact L)) + fact N * (S M (fact L) + fact L + N * quo (fact L) M))) := by
    ipra_le sl t + sl sw
  exact le_congr (congrMul hNp (.eqRefl _)) (congrMul hNp (.eqRefl _)) c

end LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertensLower
