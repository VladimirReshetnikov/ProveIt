import IPRADerivations.AnalyticNumberTheory.HarmonicMertens

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

namespace LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertensLower

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.LogElementary (log_upper)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev
  (S_mono wt Hy trace_readback_congr trace_stationary trace_factor_readback trace_end_readback)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (subadd le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLambda (Sw harmonic_sandwich)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorTrace (trT tr_zero lpf_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (Lw)
open LeanProofs.IPRA.Analysis.Products (fact)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## `λ_M(m) ≤ L_w(m) + m/M` along the trace -/

/-- The invariant `S(Mm) + L_w(x_i) ≤ S(M x_i) + L_w(m) + i ⌊F/M⌋`. -/
abbrev K (m M L i : PTm n) : Fm PTm n :=
  le (S (M * m) (fact L) + Lw wt (trT i m) (pairT M (fact L)))
    (S (M * trT i m) (fact L) + Lw wt m (pairT M (fact L)) + i * quo (fact L) M)

theorem k_zero (m M L : PTm n) : Γ ⊢[PRAAx] K m M L zero := by
  have terms := trace_readback_congr M (fact L) (tr_zero (Γ := Γ) m)
  ipra_le 0 with natEq terms.andE₂ - natEq terms.andE₁

theorem k_step {m M L i : PTm n} (hm : Γ ⊢[PRAAx] le one m) (hM : Γ ⊢[PRAAx] le one M)
    (hL : Γ ⊢[PRAAx] le (M * m) L) (ih : Γ ⊢[PRAAx] K m M L i) : Γ ⊢[PRAAx] K m M L (succ i) := by
  refine .orE (lt_or_le one (trT i m)) ?_ ?_
  · let Δ := lt one (trT i m) :: Γ
    have hx : Δ ⊢[PRAAx] le two (trT i m) := Prf.hyp0
    have factor := trace_factor_readback (Γ := Δ) i hm.wk hL.wk hx
    have bound := subadd (pos_of_lt_zero (Γ := Δ) hM.wk) (lpf_pos _) factor.andE₁ factor.andE₂.andE₁
    have terms := factor.andE₂.andE₂
    ipra_le sl ih.wk + sl bound with natEq terms.andE₂.andE₁ - natEq terms.andE₁ - natEq terms.andE₂.andE₂
  · have terms := trace_readback_congr M (fact L) (trace_stationary i hm.wk Prf.hyp0)
    ipra_le sl ih.wk + 𝔞 (quo (fact L) M) with natEq terms.andE₂ - natEq terms.andE₁

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
  have terms := trace_end_readback M (fact L) hm
  ipra_le sl I with natEq terms.andE₁ - natEq terms.andE₂

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

export_ipra AnalyticNumberTheory.HarmonicMertensLower (delta_le)
