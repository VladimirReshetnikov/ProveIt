import IPRADerivations.AnalyticNumberTheory.PrimeRank

/-!
# Arbitrarily long runs of composite numbers

Packet: `analytic-number-theory/prime-counting-ipra`, `sections/foundations.tex`, after the Theorem "Rank and
inverse rank": "Arbitrarily long constant stretches also have PR witnesses ... each integer `(s + 2)! + j` for
`2 ≤ j ≤ s + 2` is composite".

* `prime_no_divisor`: a prime has no divisor `d` with `2 ≤ d < p`;
* **`composite_run`**: `N! + j` is not prime for `2 ≤ j ≤ N` (it is divisible by `j`, and `j < N! + j`);
* `gap_step`: `π(N! + t + 2) = π(N! + t + 1)` for `t + 2 ≤ N`;
* **`pc_run`**: `π(N! + t + 1) = π(N! + 1)` for `t + 1 ≤ N`: the prime count is constant on
  `[N! + 1, N! + N]`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PrimeGaps

open_ipra exports
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime dvd_fact fact_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PrimeRank (pc pc_succ congrPc pc_step_le succ_le_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- A prime has no divisor `d` with `2 ≤ d < p`. -/
theorem prime_no_divisor {p d : PTm n} (hp : Γ ⊢[PRAAx] prime p) (h2 : Γ ⊢[PRAAx] le two d)
    (hlt : Γ ⊢[PRAAx] lt d p) : Γ ⊢[PRAAx] neg (dvd d p) := by
  have hp' := hp
  unfold prime at hp'
  have a := Prf.allE d (Prf.andE₂ hp')
  simp only [Fm.subst_imp, subst_le, subst_lt, subst_neg, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at a
  exact Prf.impE (Prf.impE a h2) hlt

theorem lt_add_pos {f j : PTm n} (fp : Γ ⊢[PRAAx] f ≐ succ (pred f)) : Γ ⊢[PRAAx] lt j (f + j) :=
  le_congr ((succ_add zero j).eqTrans (congrSucc (zero_add j))) (.eqRefl _)
    (add_le_add_right j (Common.one_le_of_pos fp))

/-- `N! + j` is not prime for `2 ≤ j ≤ N`. -/
theorem composite_run {N j : PTm n} (h2 : Γ ⊢[PRAAx] le two j) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] isP (fact N + j) ≐ zero := by
  have hj1 := p_pos h2
  have df : Γ ⊢[PRAAx] dvd j (fact N) := dvd_congr_left hj1.eqSymm (dvd_fact (le_congr hj1 (.eqRefl _) hj))
  have dj : Γ ⊢[PRAAx] dvd j j := dvd_congr_left hj1.eqSymm (dvd_congr hj1.eqSymm (dvd_self (pred j)))
  have dN : Γ ⊢[PRAAx] dvd j (fact N + j) := dvd_add' hj1 df dj
  have hlt : Γ ⊢[PRAAx] lt j (fact N + j) := lt_add_pos (fact_pos N)
  refine .orE (isP_01 (fact N + j)) Prf.hyp0 ?_
  have hp := prime_of_isP (Γ := (isP (fact N + j) ≐ one) :: Γ) Prf.hyp0
  exact .botE _ (.impE (prime_no_divisor hp h2.wk hlt.wk) dN.wk)

theorem two_le_ss (t : PTm n) : Γ ⊢[PRAAx] le two (succ (succ t)) :=
  le_of_eq_add (d := t) (by ipra_ring)

/-- `π(N! + t + 2) = π(N! + t + 1)` for `t + 2 ≤ N`. -/
theorem gap_step {N t : PTm n} (h : Γ ⊢[PRAAx] le (succ (succ t)) N) :
    Γ ⊢[PRAAx] pc (fact N + succ (succ t)) ≐ pc (fact N + succ t) := by
  have es : Γ ⊢[PRAAx] fact N + succ (succ t) ≐ succ (fact N + succ t) := add_succ _ _
  have z : Γ ⊢[PRAAx] isP (succ (fact N + succ t)) ≐ zero :=
    (congrIsP es.eqSymm).eqTrans (composite_run (two_le_ss t) h)
  exact (congrPc es).eqTrans ((pc_succ _).eqTrans ((congrAdd (.eqRefl _) z).eqTrans (add_zero _)))

/-- Variables: `0 = t`, `1 = N`. -/
abbrev runF : Fm PTm 2 :=
  le (succ (var 0)) (var 1) ⟶ (pc (fact (var 1) + succ (var 0)) ≐ pc (fact (var 1) + one))

theorem run_open : ([] : List (Fm PTm 2)) ⊢[PRAAx] runF := by
  ipra_ind (⟨le_QF _ _, trivial⟩) [subst_le, subst_ap2]
  · exact .impI (.eqRefl _)
  · refine .impI ?_
    have h : (le (succ (succ (var 0))) (var 1) :: [runF]) ⊢[PRAAx] le (succ (succ (var 0))) (var 1) := Prf.hyp0
    have h' : (le (succ (succ (var 0))) (var 1) :: [runF]) ⊢[PRAAx] le (succ (var 0)) (var 1) :=
      le_trans (le_succ_self _) h
    exact (gap_step h).eqTrans (.impE Prf.hyp1 h')

/-- The prime count is constant on `[N! + 1, N! + N]`: `π(N! + t + 1) = π(N! + 1)` for `t + 1 ≤ N`. -/
theorem pc_run {N t : PTm n} (h : Γ ⊢[PRAAx] le (succ t) N) :
    Γ ⊢[PRAAx] pc (fact N + succ t) ≐ pc (fact N + one) := by
  have i := inst (Γ := Γ) run_open (![t, N] : Fin 2 → PTm n)
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, PTm.subst_add, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at i
  exact .impE i h

/-! ## The increments of the prime count -/

/-- `π(u + j) ≤ π(u) + j`: with `PrimeRank.pc_mono`, `0 ≤ π(v) − π(u) ≤ v − u` for `u ≤ v`. -/
theorem pc_lipschitz (u j : PTm n) : Γ ⊢[PRAAx] le (pc (u + j)) (pc u + j) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (pc (Syn.shift u + var 0)) (pc (Syn.shift u) + var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_le, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      exact le_congr (congrPc (add_zero u).eqSymm) (add_zero _).eqSymm (le_refl _)
    · simp only [subst_le, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      let D : List (Fm PTm (n + 1)) :=
        le (pc (Syn.shift u + var 0)) (pc (Syn.shift u) + var 0) :: Γ.map Fm.shift
      have ih : D ⊢[PRAAx] le (pc (Syn.shift u + var 0)) (pc (Syn.shift u) + var 0) := Prf.hyp0
      have es : D ⊢[PRAAx] Syn.shift u + succ (var 0) ≐ succ (Syn.shift u + var 0) := add_succ _ _
      have es2 : D ⊢[PRAAx] pc (Syn.shift u) + succ (var 0) ≐ succ (pc (Syn.shift u) + var 0) := add_succ _ _
      exact le_congr (congrPc es.eqSymm) es2.eqSymm (le_trans (pc_step_le _) (succ_le_succ ih))
  have r := Prf.allE j hall
  simp only [subst_le, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at r
  exact r

end LeanProofs.IPRA.AnalyticNumberTheory.PrimeGaps
