import IPRADerivations.AnalyticNumberTheory.FactorVector

/-!
# The least-factor trace

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Lemma `lem:factor-trace`:
the primitive-recursive trace `x₀ = n`, `x_{i+1} = x_i / ℓ(x_i)` for `x_i > 1` and `1` otherwise
(`ℓ` the least prime factor) reaches `1` by stage `n` for `n > 0`, every nontrivial factor it
selects is prime, and `n = ∏_{p ≤ n} p^{v_p(n)}`.

* `trT i n`: the trace, by primitive recursion with the step `x ↦ ⌊x/ℓ(x)⌋ + [x ≤ 1]`, which is
  `x/ℓ(x)` for `x ≥ 2` (`step_big`) and `1` for `x ≤ 1` (`step_small`);
* `trace_prime`: when `x_i ≥ 2`, `ℓ(x_i)` is prime and `x_{i+1} · ℓ(x_i) = x_i`; `trace_lt`:
  then `x_{i+1} < x_i`;
* `trace_bound`: the quantifier-free invariant `i ≤ n → x_i + i ≤ n + 1`, by induction on `i`;
* `trace_end`: `x_n = 1` for `n ≥ 1`;
* `factor_product`: `n = ∏_{p<n+1} p^{v_p(n)}` (`FactorVector.reconstruct`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.FactorTrace

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (lpf prime)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (two_eq lpf_dvd' lpf_prime' reconstruct R)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (quo_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (eq_succ_pred)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' pos_of_eq_mul one_le_of_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The step `x ↦ ⌊x/ℓ(x)⌋ + [x ≤ 1]`. -/
abbrev stepT (x : PTm n) : PTm n := quo x (lpf x) + monus one (monus x one)

/-- Variables: `0 = i`, `1 = x_i`, `2 = n`. -/
abbrev stepB : PTm 3 := stepT (var 1)
abbrev trF : PR 2 := rec2 (var 0) stepB
/-- The trace `x_i` of `n`. -/
abbrev trT (i N : PTm n) : PTm n := ap2 trF i N

theorem tr_zero (N : PTm n) : Γ ⊢[PRAAx] trT zero N ≐ N := by
  simpa using rec2_zero (Γ := Γ) (var 0) stepB N

theorem tr_succ (i N : PTm n) : Γ ⊢[PRAAx] trT (succ i) N ≐ stepT (trT i N) := by
  simpa using rec2_succ (Γ := Γ) (var 0) stepB i N

/-! ## The step -/

theorem lpf_two (x : PTm n) : Γ ⊢[PRAAx] le two (lpf x) :=
  (succ_monus_succ _ _).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _))

theorem lpf_pos (x : PTm n) : Γ ⊢[PRAAx] lpf x ≐ succ (pred (lpf x)) := congrSucc (pred_succ _).eqSymm

theorem step_big {x : PTm n} (hx : Γ ⊢[PRAAx] le two x) :
    Γ ⊢[PRAAx] (stepT x ≐ quo x (lpf x)) ⋏ (x ≐ lpf x * quo x (lpf x)) := by
  have e := two_eq hx
  have c : Γ ⊢[PRAAx] monus x one ≐ succ (monus x two) :=
    (congrMonus e (.eqRefl _)).eqTrans ((succ_monus_succ _ _).eqTrans (monus_zero _))
  have l₁ : Γ ⊢[PRAAx] monus one (monus x one) ≐ zero :=
    (congrMonus (.eqRefl one) c).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _))
  exact .andI ((congrAdd (.eqRefl _) l₁).eqTrans (add_zero _)) (eq_of_dvd' (lpf_pos x) (lpf_dvd' hx))

theorem step_small {x : PTm n} (hx : Γ ⊢[PRAAx] le x one) : Γ ⊢[PRAAx] stepT x ≐ one := by
  have hlt : Γ ⊢[PRAAx] lt x (lpf x) := le_trans ((succ_monus_succ _ _).eqTrans hx) (lpf_two x)
  have q₀ : Γ ⊢[PRAAx] quo x (lpf x) ≐ zero :=
    quo_eq (lpf_pos x) (by apply deriveNat; ipra_simps; ring) hlt
  have m₀ : Γ ⊢[PRAAx] monus one (monus x one) ≐ one :=
    (congrMonus (.eqRefl one) hx).eqTrans (monus_zero _)
  exact (congrAdd q₀ m₀).eqTrans (zero_add _)

theorem two_pos {x : PTm n} (hx : Γ ⊢[PRAAx] le two x) : Γ ⊢[PRAAx] x ≐ succ (pred x) :=
  eq_succ_pred (two_eq hx)

theorem step_pos (x : PTm n) : Γ ⊢[PRAAx] le one (stepT x) := by
  refine .orE (lt_or_le one x) ?_ ?_
  · have b := step_big (Prf.hyp0 : (lt one x :: Γ) ⊢[PRAAx] le two x)
    have hq := pos_of_eq_mul (two_pos Prf.hyp0) (Prf.andE₂ b)
    exact le_congr (.eqRefl _) (Prf.andE₁ b).eqSymm (one_le_of_pos hq)
  · exact le_congr (.eqRefl _) (step_small Prf.hyp0).eqSymm (le_refl _)

/-- For `x ≥ 2`, `x/ℓ(x) + 1 ≤ x`. -/
theorem quo_succ_le {x : PTm n} (hx : Γ ⊢[PRAAx] le two x) : Γ ⊢[PRAAx] le (succ (quo x (lpf x))) x := by
  have b := step_big hx
  have hq := natEq (pos_of_eq_mul (two_pos hx) (Prf.andE₂ b))
  have eX := natEq (Prf.andE₂ b)
  have eL := natEq (eq_add_of_le (lpf_two (Γ := Γ) x))
  refine le_of_eq_add (d := pred (quo x (lpf x)) + monus (lpf x) two * quo x (lpf x)) ?_
  apply deriveNat; ipra_simps
  linear_combination eX + 𝔞 (quo x (lpf x)) * eL + hq

theorem step_bound {x i N : PTm n} (h : Γ ⊢[PRAAx] le (succ i) N) (ih : Γ ⊢[PRAAx] le (x + i) (succ N)) :
    Γ ⊢[PRAAx] le (stepT x + succ i) (succ N) := by
  refine .orE (lt_or_le one x) ?_ ?_
  · have hx : (lt one x :: Γ) ⊢[PRAAx] le two x := Prf.hyp0
    have l := quo_succ_le hx
    have w := natEq (eq_add_of_le l)
    have l' : (lt one x :: Γ) ⊢[PRAAx] le (stepT x + succ i) (x + i) := by
      refine le_congr (congrAdd (Prf.andE₁ (step_big hx)).eqSymm (.eqRefl _)) (.eqRefl _) ?_
      refine le_of_eq_add (d := monus x (succ (quo x (lpf x)))) ?_
      apply deriveNat; ipra_simps
      linear_combination w
    exact le_trans l' ih.wk
  · have s := step_small (Prf.hyp0 : (le x one :: Γ) ⊢[PRAAx] le x one)
    have h₂ : (le x one :: Γ) ⊢[PRAAx] le (succ (succ i)) (succ N) := (succ_monus_succ _ _).eqTrans h.wk
    refine le_congr ?_ (.eqRefl _) h₂
    exact (by apply deriveNat; ipra_simps; ring : (le x one :: Γ) ⊢[PRAAx] succ (succ i) ≐ one + succ i).eqTrans
      (congrAdd s.eqSymm (.eqRefl _))

/-! ## The invariant -/

/-- Variables: `0 = i`, `1 = n`. -/
private abbrev bndF : Fm PTm 2 := le (var 0) (var 1) ⟶ le (trT (var 0) (var 1) + var 0) (succ (var 1))

private theorem bnd₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] bndF := by
  refine ind _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
  · simp only [Fm.subst_imp, subst_le, PTm.subst_add, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact .impI (le_congr ((tr_zero _).eqSymm.eqTrans (add_zero _).eqSymm) (.eqRefl _) (le_succ_self _))
  · simp only [Fm.subst_imp, subst_le, PTm.subst_add, subst_ap2, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine .impI ?_
    have hi : (le (succ (var 0)) (var 1) :: [bndF]) ⊢[PRAAx] le (var 0 : PTm 2) (var 1) :=
      le_trans (le_succ_self _) Prf.hyp0
    have ih := Prf.impE Prf.hyp1 hi
    exact le_congr (congrAdd (tr_succ _ _).eqSymm (.eqRefl _)) (.eqRefl _) (step_bound Prf.hyp0 ih)

/-- `i ≤ n → x_i + i ≤ n + 1`. -/
theorem trace_bound (i N : PTm n) : Γ ⊢[PRAAx] le i N ⟶ le (trT i N + i) (succ N) := by
  simpa using inst (Γ := Γ) bnd₀ (![i, N] : Fin 2 → PTm n)

/-- The trace reaches `1` by stage `n`, for `n ≥ 1`. -/
theorem trace_end {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) : Γ ⊢[PRAAx] trT N N ≐ one := by
  have b := Prf.impE (trace_bound (Γ := Γ) N N) (le_refl N)
  have w := natEq (eq_add_of_le b)
  have up : Γ ⊢[PRAAx] le (trT N N) one := by
    refine le_of_eq_add (d := monus (succ N) (trT N N + N)) ?_
    apply deriveNat; ipra_simps
    linear_combination w
  have lo : Γ ⊢[PRAAx] le one (trT N N) :=
    le_congr (.eqRefl _) ((tr_succ (pred N) N).eqSymm.eqTrans (congrAp2 trF hN.eqSymm (.eqRefl N)))
      (step_pos _)
  exact le_antisymm up lo

/-- Every nontrivial factor selected is prime, and it divides off exactly. -/
theorem trace_prime {i N : PTm n} (h : Γ ⊢[PRAAx] le two (trT i N)) :
    Γ ⊢[PRAAx] prime (lpf (trT i N)) ⋏ (trT (succ i) N * lpf (trT i N) ≐ trT i N) := by
  have b := step_big h
  refine .andI (lpf_prime' h) ?_
  exact (congrMul ((tr_succ i N).eqTrans (Prf.andE₁ b)) (.eqRefl _)).eqTrans ((mul_comm _ _).eqTrans (Prf.andE₂ b).eqSymm)

/-- While `x_i ≥ 2`, the trace strictly decreases. -/
theorem trace_lt {i N : PTm n} (h : Γ ⊢[PRAAx] le two (trT i N)) : Γ ⊢[PRAAx] lt (trT (succ i) N) (trT i N) :=
  le_congr (congrSucc ((Prf.andE₁ (step_big h)).eqSymm.eqTrans (tr_succ i N).eqSymm)) (.eqRefl _) (quo_succ_le h)

/-- `n = ∏_{p<n+1} p^{v_p(n)}` for `n ≥ 1`. -/
theorem factor_product {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) : Γ ⊢[PRAAx] R (succ N) N ≐ N :=
  reconstruct hN (monus_self _)

end LeanProofs.IPRA.AnalyticNumberTheory.FactorTrace
