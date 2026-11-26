import IPRADerivations.AnalyticNumberTheory.LogRefinement
import IPRADerivations.AnalyticNumberTheory.HarmonicLogPow2
import IPRADerivations.AnalyticNumberTheory.FactorTrace
import IPRADerivations.AnalyticNumberTheory.PrimePowerMangoldt
import IPRADerivations.AnalyticNumberTheory.ChebyshevBounds
import IPRADerivations.AnalyticNumberTheory.MuLambda
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# Chebyshev's bound for the harmonic logarithm (`pnt_ipra_constructive_2026-11-14`, `con:global`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, hypothesis `con:global`
(`|r(t)| ≤ 4`, `r(t) = e^{-t}(ψ(e^t) − e^t)`), i.e. `0 ≤ ψ(x) ≤ 5x`; the packet's route is Chebyshev's
`ψ(x) ≤ 4x log 2 ≤ 4x`. `ChebyshevBounds.lcmu_upper` gives the integer form `lcm(1, …, N) ≤ 2^{4N}`; this
module carries it to the packet's rational logarithm `λ_M(a) = H_{Ma} − H_M` (common denominator
`F = L!`, `H_m = S(m, F)/F`) **with no passage to real limits** (the repository's finite-stage convention):

* `superadd`: `λ_M(ab) ≥ λ_M(a) + λ_M(b)` — the first conjunct of `LogRefinement.log_refine`;
* `S_mono`: the harmonic sum is monotone in its length;
* `wt`: the weight `w(q; M, F) = S(Mq) ∸ S(M)`, i.e. `Λ_w(p^a) = λ_M(p)`; `lw_prime`: `L_w(p) = λ_M(p)`;
* `harmonic_lw`: `L_w(m) ≤ λ_M(m)` for `1 ≤ m`, `Mm ≤ L` — one QF induction along the least-prime-factor
  trace `x_{i+1} ℓ(x_i) = x_i` (`FactorTrace`) with the invariant `L_w(m) + S(M x_i) ≤ S(Mm) + L_w(x_i)`;
* `psi_le` (`con:global`, Chebyshev form): `ψ_w(N) = ∑_{d ≤ N} Λ_w(d) ≤ 4N`, i.e.
  `∑_{p^a ≤ N} λ_M(p) ≤ 4N` at every mesh `M ≥ 1` with `L ≥ M 2^{4N}` — from `psi_lcm`, `harmonic_lw`,
  `lcmu_upper` and `HarmonicLogPow2.S_pow2` (`λ_M(2^m) ≤ m`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.LogRefinement (log_refine)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogPow2 (S_pow2)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorTrace (trT trF tr_zero tr_succ step_pos step_small trace_prime
  trace_lt trace_end lpf_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (lpf prime)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (ellB Lw)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (congrLw lw_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (lcmu lcmu_pos Psi psi_lcm pos_of_lt_zero lt_zero_of_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds (lcmu_upper)
open LeanProofs.IPRA.Analysis.Products (fact)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Monotonicity and superadditivity -/

/-- The harmonic sum is monotone in its length. -/
theorem S_mono {a b : PTm n} (F : PTm n) (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (S a F) (S b F) := by
  have e2 := natEq (congrAp2 (Γ := Γ) (sumF hB) (eq_add_of_le h) (.eqRefl F))
  have s := natEq (sum_split (Γ := Γ) hB a (monus b a) F)
  ipra_le 𝔞 (ap2 (sumF (offB hB)) (monus b a) (pairT a F)) with e2 + s

/-- Superadditivity of the harmonic logarithm: `λ_M(a) + λ_M(b) ≤ λ_M(ab)`, i.e.
`S(Ma) + S(Mb) ≤ S(Mab) + S(M)` at the mesh `F = L!`, `Mab ≤ L`. -/
theorem superadd {M a b L : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) (hL : Γ ⊢[PRAAx] le (M * (a * b)) L) :
    Γ ⊢[PRAAx] le (S (M * a) (fact L) + S (M * b) (fact L)) (S (M * (a * b)) (fact L) + S M (fact L)) := by
  have wM := natEq hM; have wb := natEq hb
  have q1 : Γ ⊢[PRAAx] M * (a * b) ≐ a * (succ (pred M) + M * pred b) := by
    ipra_lc 𝔞 a * wM + 𝔞 a * 𝔞 M * wb
  have hL' : Γ ⊢[PRAAx] le (a * (succ (pred M) + M * pred b)) L := le_congr q1 (.eqRefl _) hL
  have r := Prf.andE₁ (log_refine (c₁ := pred M) (T := M * pred b) ha hL')
  have q2 : Γ ⊢[PRAAx] M * b ≐ succ (pred M) + M * pred b := by
    ipra_lc wM + 𝔞 M * wb
  have q3 : Γ ⊢[PRAAx] M * a ≐ a * succ (pred M) := by
    ipra_lc 𝔞 a * wM
  have fab := natEq (congrAp2 (Γ := Γ) (sumF hB) q1 (.eqRefl (fact L)))
  have fb := natEq (congrAp2 (Γ := Γ) (sumF hB) q2 (.eqRefl (fact L)))
  have fa := natEq (congrAp2 (Γ := Γ) (sumF hB) q3 (.eqRefl (fact L)))
  have fM := natEq (congrAp2 (Γ := Γ) (sumF hB) hM (.eqRefl (fact L)))
  ipra_le sl r with fa + fb - fab - fM

/-! ## The harmonic-logarithm weight -/

/-- `w(q; (M, F)) = S(Mq, F) ∸ S(M, F)`, i.e. `Λ_w(p^a) = λ_M(p)`. -/
def wt : PTm 2 := monus (S (fstT (var 1) * var 0) (sndT (var 1))) (S (fstT (var 1)) (sndT (var 1)))

theorem inst2_wt (q z : PTm n) : inst2 wt q z = monus (S (fstT z * q) (sndT z)) (S (fstT z) (sndT z)) := by
  simp [wt, inst2]

theorem wt_at (q M F : PTm n) : Γ ⊢[PRAAx] inst2 wt q (pairT M F) ≐ monus (S (M * q) F) (S M F) := by
  rw [inst2_wt]
  exact congrMonus (congrAp2 (sumF hB) (congrMul (fst_pair _ _) (.eqRefl _)) (snd_pair _ _))
    (congrAp2 (sumF hB) (fst_pair _ _) (snd_pair _ _))

/-- `L_w(p) = λ_M(p)` for a prime `p`. -/
theorem lw_prime {p : PTm n} (M F : PTm n) (hp : Γ ⊢[PRAAx] prime p) :
    Γ ⊢[PRAAx] Lw wt p (pairT M F) ≐ monus (S (M * p) F) (S M F) := by
  have e1 : Γ ⊢[PRAAx] pw p one ≐ p := (pw_succ p zero).eqTrans ((congrMul (pw_zero p) (.eqRefl p)).eqTrans (one_mul p))
  have h1 : Γ ⊢[PRAAx] (one : PTm n) ≐ succ (pred one) := congrSucc (pred_succ _).eqSymm
  refine (congrLw (w := wt) (pairT M F) e1.eqSymm).eqTrans ((PrimePowerMangoldt.lw_pw (w := wt) hp h1 _).eqTrans ?_)
  exact (one_mul _).eqTrans ((congrMul (Valuation.isP_of_prime hp) (.eqRefl _)).eqTrans ((one_mul _).eqTrans (wt_at _ _ _)))

/-! ## The trace stays in `[1, m]` -/

/-- Variables: `0 = i`, `1 = m`. -/
private abbrev posF : Fm PTm 2 := le one (var 1) ⟶ le one (trT (var 0) (var 1))

private theorem pos₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] posF := by
  ipra_ind (⟨le_QF _ _, le_QF _ _⟩) [subst_le, subst_ap2]
  · exact .impI (le_congr (.eqRefl _) (tr_zero _).eqSymm Prf.hyp0)
  · exact .impI (le_congr (.eqRefl _) (tr_succ _ _).eqSymm (step_pos _))

theorem tr_pos {m : PTm n} (hm : Γ ⊢[PRAAx] le one m) (i : PTm n) : Γ ⊢[PRAAx] le one (trT i m) := by
  have h := inst (Γ := Γ) pos₀ (![i, m] : Fin 2 → PTm n)
  simp at h
  exact Prf.impE h hm

/-- Variables: `0 = i`, `1 = m`. -/
private abbrev boundF : Fm PTm 2 := le one (var 1) ⟶ le (trT (var 0) (var 1)) (var 1)

private theorem bound₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] boundF := by
  ipra_ind (⟨le_QF _ _, le_QF _ _⟩) [subst_le, subst_ap2]
  · exact .impI (le_congr (tr_zero _).eqSymm (.eqRefl _) (le_refl _))
  · refine .impI ?_
    have ih : (le one (var 1) :: [boundF]) ⊢[PRAAx] le (trT (var 0) (var 1)) (var 1) := Prf.impE Prf.hyp1 Prf.hyp0
    refine .orE (lt_or_le one (trT (var 0) (var 1))) ?_ ?_
    · exact le_trans (le_trans (le_succ_self _) (trace_lt Prf.hyp0)) ih.wk
    · have s : (le (trT (var 0) (var 1)) one :: le one (var 1) :: [boundF]) ⊢[PRAAx]
          trT (succ (var 0)) (var 1) ≐ one := (tr_succ _ _).eqTrans (step_small Prf.hyp0)
      exact le_congr s.eqSymm (.eqRefl _) Prf.hyp1

theorem tr_le {m : PTm n} (hm : Γ ⊢[PRAAx] le one m) (i : PTm n) : Γ ⊢[PRAAx] le (trT i m) m := by
  have h := inst (Γ := Γ) bound₀ (![i, m] : Fin 2 → PTm n)
  simp at h
  exact Prf.impE h hm

/-! ## `L_w(m) ≤ λ_M(m)` along the trace -/

/-- Read back equal trace positions in the harmonic and weighted Mangoldt sums. -/
theorem trace_readback_congr (M F : PTm n) {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] (S (M * a) F ≐ S (M * b) F) ⋏ (Lw wt a (pairT M F) ≐ Lw wt b (pairT M F)) :=
  .andI (congrAp2 (sumF hB) (congrMul (.eqRefl _) h) (.eqRefl _)) (congrLw (w := wt) _ h)

/-- A positive trace is stationary once it is at most one. -/
theorem trace_stationary (i : PTm n) {m : PTm n} (hm : Γ ⊢[PRAAx] le one m)
    (h : Γ ⊢[PRAAx] le (trT i m) one) : Γ ⊢[PRAAx] trT (succ i) m ≐ trT i m :=
  ((tr_succ i m).eqTrans (step_small h)).eqTrans (le_antisymm h (tr_pos hm i)).eqSymm

/-- The active trace step supplies the shared bounds and exact changes in both sums. -/
theorem trace_factor_readback (i : PTm n) {m M L : PTm n} (hm : Γ ⊢[PRAAx] le one m)
    (hL : Γ ⊢[PRAAx] le (M * m) L) (hx : Γ ⊢[PRAAx] le two (trT i m)) :
    let a := trT i m
    let b := trT (succ i) m
    let p := lpf a
    let F := fact L
    let z := pairT M F
    let d := monus (S (M * p) F) (S M F)
    Γ ⊢[PRAAx] (b ≐ succ (pred b)) ⋏ le (M * (p * b)) L ⋏
      (S (M * (p * b)) F ≐ S (M * a) F) ⋏ (S (M * p) F ≐ S M F + d) ⋏
      (Lw wt a z ≐ d + Lw wt b z) := by
  have step := trace_prime hx
  have positive := pos_of_lt_zero (tr_pos hm (succ i))
  have primePositive := lpf_pos (Γ := Γ) (trT i m)
  have scale := congrMul (.eqRefl M) ((mul_comm _ _).eqTrans step.andE₂)
  have within := le_congr scale.eqSymm (.eqRefl _) (le_trans (mul_le_mul_left M (tr_le hm i)) hL)
  have monotone := le_congr (Common.mul_one_right M) (.eqRefl _)
    (mul_le_mul_left M (Common.one_le_of_pos primePositive))
  have split := (congrLw (w := wt) (pairT M (fact L)) (step.andE₂.eqSymm.eqTrans (mul_comm _ _))).eqTrans
    ((lw_mul (w := wt) primePositive positive).eqTrans (congrAdd (lw_prime M (fact L) step.andE₁) (.eqRefl _)))
  exact .andI positive (.andI within (.andI (congrAp2 (sumF hB) scale (.eqRefl _))
    (.andI (eq_add_of_le (S_mono (fact L) monotone)) split)))

/-- At the terminal trace, the harmonic sum is `S(M)` and the weighted sum is zero. -/
theorem trace_end_readback (M F : PTm n) {m : PTm n} (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] (S (M * trT m m) F ≐ S M F) ⋏ (Lw wt (trT m m) (pairT M F) ≐ zero) := by
  have terms := trace_readback_congr M F (trace_end (pos_of_lt_zero hm))
  exact .andI (terms.andE₁.eqTrans (congrAp2 (sumF hB) (Common.mul_one_right M) (.eqRefl _)))
    (terms.andE₂.eqTrans (MuLambda.lw_one (w := wt) _))

/-- The invariant `L_w(m) + S(M x_i) ≤ S(Mm) + L_w(x_i)`. -/
abbrev J (m M L i : PTm n) : Fm PTm n :=
  le (Lw wt m (pairT M (fact L)) + S (M * trT i m) (fact L)) (S (M * m) (fact L) + Lw wt (trT i m) (pairT M (fact L)))

theorem j_zero (m M L : PTm n) : Γ ⊢[PRAAx] J m M L zero := by
  have terms := trace_readback_congr M (fact L) (tr_zero (Γ := Γ) m)
  ipra_le 0 with natEq terms.andE₁ - natEq terms.andE₂

theorem j_step {m M L i : PTm n} (hm : Γ ⊢[PRAAx] le one m) (hM : Γ ⊢[PRAAx] le one M)
    (hL : Γ ⊢[PRAAx] le (M * m) L) (ih : Γ ⊢[PRAAx] J m M L i) : Γ ⊢[PRAAx] J m M L (succ i) := by
  refine .orE (lt_or_le one (trT i m)) ?_ ?_
  · let Δ := lt one (trT i m) :: Γ
    have hx : Δ ⊢[PRAAx] le two (trT i m) := Prf.hyp0
    have factor := trace_factor_readback (Γ := Δ) i hm.wk hL.wk hx
    have bound := superadd (pos_of_lt_zero (Γ := Δ) hM.wk) (lpf_pos _) factor.andE₁ factor.andE₂.andE₁
    have terms := factor.andE₂.andE₂
    ipra_le sl ih.wk + sl bound with natEq terms.andE₁ - natEq terms.andE₂.andE₁ + natEq terms.andE₂.andE₂
  · have terms := trace_readback_congr M (fact L) (trace_stationary i hm.wk Prf.hyp0)
    ipra_le sl ih.wk with natEq terms.andE₁ - natEq terms.andE₂

/-- Hypotheses of the trace induction. -/
abbrev Hy (m M L : PTm n) : Fm PTm n := le one m ⋏ (le one M ⋏ le (M * m) L)

/-- Variables: `0 = i`, `1 = m`, `2 = M`, `3 = L`. -/
private abbrev mainF : Fm PTm 4 := Hy (var 1) (var 2) (var 3) ⟶ J (var 1) (var 2) (var 3) (var 0)

private theorem main₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] mainF := by
  ipra_ind (⟨⟨le_QF _ _, le_QF _ _, le_QF _ _⟩, le_QF _ _⟩) [subst_le, subst_ap2, subst_pairT]
  · exact .impI (j_zero _ _ _)
  · refine .impI ?_
    have h := (Prf.hyp0 : (Hy (var 1) (var 2) (var 3) :: [mainF]) ⊢[PRAAx] Hy (var 1) (var 2) (var 3))
    exact j_step (Prf.andE₁ h) (Prf.andE₁ (Prf.andE₂ h)) (Prf.andE₂ (Prf.andE₂ h)) (Prf.impE Prf.hyp1 Prf.hyp0)

/-- `L_w(m) ≤ λ_M(m)`: `L_w(m) + S(M) ≤ S(Mm)` for `1 ≤ m`, `1 ≤ M`, `Mm ≤ L`, at the mesh `F = L!`. -/
theorem harmonic_lw {m M L : PTm n} (hm : Γ ⊢[PRAAx] le one m) (hM : Γ ⊢[PRAAx] le one M)
    (hL : Γ ⊢[PRAAx] le (M * m) L) :
    Γ ⊢[PRAAx] le (Lw wt m (pairT M (fact L)) + S M (fact L)) (S (M * m) (fact L)) := by
  have i := inst (Γ := Γ) main₀ (![m, m, M, L] : Fin 4 → PTm n)
  simp at i
  have I : Γ ⊢[PRAAx] J m M L m := Prf.impE i (.andI hm (.andI hM hL))
  have terms := trace_end_readback M (fact L) hm
  ipra_le sl I with natEq terms.andE₂ - natEq terms.andE₁

/-! ## `con:global`: Chebyshev's bound -/

/-- `con:global`, Chebyshev form: `ψ_w(N) = ∑_{d ≤ N} Λ_w(d) ≤ 4N F`, i.e. `∑_{p^a ≤ N} λ_M(p) ≤ 4N`, at
every mesh `M ≥ 1` with denominator `F = L!`, `M 2^{4N} ≤ L`. -/
theorem psi_le {N M L : PTm n} (hM : Γ ⊢[PRAAx] le one M) (hL : Γ ⊢[PRAAx] le (M * pw two (two * (two * N))) L) :
    Γ ⊢[PRAAx] le (Psi wt N (pairT M (fact L))) (two * (two * N) * fact L) := by
  have lu := lcmu_upper (Γ := Γ) N
  have mono : Γ ⊢[PRAAx] le (M * lcmu N) (M * pw two (two * (two * N))) := by
    refine le_of_eq_add (d := M * monus (pw two (two * (two * N))) (lcmu N)) ?_
    ipra_lc 𝔞 M * natEq (eq_add_of_le lu)
  have main := harmonic_lw (lt_zero_of_pos (lcmu_pos N)) hM (le_trans mono hL)
  have sm := S_mono (fact L) mono
  have sp := S_pow2 (Γ := Γ) M (fact L) (two * (two * N))
  have ps := natEq (psi_lcm (Γ := Γ) wt N (pairT M (fact L)))
  ipra_le sl main + sl sm + sl sp with ps

end LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev
