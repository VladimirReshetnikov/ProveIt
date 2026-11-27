import IPRADerivations.AnalyticNumberTheory.GoldbachGeometric
import IPRADerivations.Core.OrderCertificates

/-!
# The numerical part of the multinomial bound

Packet: `diophantine-number-theory/apery_ipra`, `apery_ipra.tex`, Lemma `lem:multibound` ("A multinomial upper
bound"): for `A = 2^22 3^15 7^7`, `M_m ≤ A^m` and `A³ < 28^41`. "Factorization of the integer bases gives the
exact identity `42^{42m} = A^m 21^{21m} 14^{14m} 6^{6m}`. Cancel the positive common factor ... `3^7 < 7^4`,
`3^10 < 2^16` ... `A³ = 2^66 3^45 7^21 < 2^82 7^41 = 28^41`."

* `pw_num`, `num_lt`: numeral powers evaluate, `pw (num a) (num b) = num (a^b)`, and `a < b` gives
  `num a < num b`;
* `cube_lt`: `A³ < 28^41`;
* `mul_pw`: `(a b)^m = a^m b^m`;
* `power_identity`: `42^{42m} = A^m (21^{21m} 14^{14m} 6^{6m})` for every `m`;
* `multibound_of_term`: the cancellation step: if the multinomial term satisfies
  `M · 21^{21m} 14^{14m} 6^{6m} ≤ 42^{42m}` (the term of `(21 + 14 + 6 + 1)^{42m}` is at most the whole sum),
  then `M ≤ A^m`. The multinomial expansion itself is not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.GoldbachGeometric (one_le_pw)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- `A = 2^22 3^15 7^7`. -/
def Aval : ℕ := 2 ^ 22 * 3 ^ 15 * 7 ^ 7

theorem pw_num (a : ℕ) : (b : ℕ) → Γ ⊢[PRAAx] pw (num a : PTm k) (num b) ≐ num (a ^ b)
  | 0 => (pw_zero _).eqTrans (by apply deriveNat; ipra_simps; simp)
  | b + 1 => (pw_succ (num a) (num b)).eqTrans ((congrMul (pw_num a b) (.eqRefl _)).eqTrans
      (by apply deriveNat; ipra_simps; push_cast; ring))

theorem num_lt (a b : ℕ) (h : a < b) : Γ ⊢[PRAAx] lt (num a : PTm k) (num b) := by
  show Γ ⊢[PRAAx] le (succ (num a)) (num b)
  refine le_of_eq_add (d := num (b - (a + 1))) ?_
  apply deriveNat; ipra_simps
  rw [Nat.cast_sub (by omega : a + 1 ≤ b)]
  push_cast; ring

/-- `A³ < 28^41`. -/
theorem cube_lt : Γ ⊢[PRAAx] lt (pw (num Aval : PTm k) (num 3)) (pw (num 28) (num 41)) :=
  lt_congr (pw_num Aval 3).eqSymm (pw_num 28 41).eqSymm (num_lt _ _ (by unfold Aval; norm_num))

/-- `(a b)^m = a^m b^m`. -/
theorem mul_pw (a b m : PTm k) : Γ ⊢[PRAAx] pw (a * b) m ≐ pw a m * pw b m := by
  have hall : Γ ⊢[PRAAx] Fm.all (pw (Syn.shift a * Syn.shift b) (Syn.var 0) ≐
      pw (Syn.shift a) (Syn.var 0) * pw (Syn.shift b) (Syn.var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero]
      have p1 := natEq (pw_zero (Γ := Γ) (a * b))
      have p2 := natEq (pw_zero (Γ := Γ) a)
      have p3 := natEq (pw_zero (Γ := Γ) b)
      apply deriveNat; ipra_simps
      rw [p1, p2, p3]; ring
    · simp only [Fm.subst_eq, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      have ih : ((pw (Syn.shift a * Syn.shift b) (Syn.var 0) ≐
          pw (Syn.shift a) (Syn.var 0) * pw (Syn.shift b) (Syn.var 0)) :: Γ.map Fm.shift) ⊢[PRAAx]
          pw (Syn.shift a * Syn.shift b) (Syn.var 0) ≐ pw (Syn.shift a) (Syn.var 0) * pw (Syn.shift b) (Syn.var 0) :=
        Prf.hyp0
      have e := natEq ih
      have p1 := natEq (pw_succ (Γ := ((pw (Syn.shift a * Syn.shift b) (Syn.var 0) ≐
          pw (Syn.shift a) (Syn.var 0) * pw (Syn.shift b) (Syn.var 0)) :: Γ.map Fm.shift)) (Syn.shift a * Syn.shift b)
          (Syn.var 0))
      have p2 := natEq (pw_succ (Γ := ((pw (Syn.shift a * Syn.shift b) (Syn.var 0) ≐
          pw (Syn.shift a) (Syn.var 0) * pw (Syn.shift b) (Syn.var 0)) :: Γ.map Fm.shift)) (Syn.shift a) (Syn.var 0))
      have p3 := natEq (pw_succ (Γ := ((pw (Syn.shift a * Syn.shift b) (Syn.var 0) ≐
          pw (Syn.shift a) (Syn.var 0) * pw (Syn.shift b) (Syn.var 0)) :: Γ.map Fm.shift)) (Syn.shift b) (Syn.var 0))
      apply deriveNat; ipra_simps
      rw [p1, p2, p3, e]; ring
  have h2 := Prf.allE m hall
  simpa only [Fm.subst_eq, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using h2

/-- `42^{42m} = A^m (21^{21m} 14^{14m} 6^{6m})`. -/
theorem power_identity (m : PTm k) :
    Γ ⊢[PRAAx] pw (num 42) (num 42 * m) ≐
      pw (num Aval) m * (pw (num 21) (num 21 * m) * pw (num 14) (num 14 * m) * pw (num 6) (num 6 * m)) := by
  have b0 : Γ ⊢[PRAAx] pw (num 42 : PTm k) (num 42) ≐
      num Aval * (pw (num 21) (num 21) * pw (num 14) (num 14) * pw (num 6) (num 6)) := by
    have e1 := natEq (pw_num (Γ := Γ) (k := k) 42 42)
    have e2 := natEq (pw_num (Γ := Γ) (k := k) 21 21)
    have e3 := natEq (pw_num (Γ := Γ) (k := k) 14 14)
    have e4 := natEq (pw_num (Γ := Γ) (k := k) 6 6)
    apply deriveNat; ipra_simps
    rw [e1, e2, e3, e4]; unfold Aval; push_cast; norm_num
  have s1 := natEq ((pw_mul (Γ := Γ) (num 42) (num 42) m).eqSymm.eqTrans
    ((congrAp2 _ (.eqRefl m) b0).eqTrans (mul_pw _ _ m)))
  have s2 := natEq (mul_pw (Γ := Γ) (pw (num 21) (num 21) * pw (num 14) (num 14)) (pw (num 6) (num 6)) m)
  have s3 := natEq (mul_pw (Γ := Γ) (pw (num 21) (num 21)) (pw (num 14) (num 14)) m)
  have t1 := natEq (pw_mul (Γ := Γ) (num 21) (num 21) m)
  have t2 := natEq (pw_mul (Γ := Γ) (num 14) (num 14) m)
  have t3 := natEq (pw_mul (Γ := Γ) (num 6) (num 6) m)
  apply deriveNat; ipra_simps
  rw [s1, s2, s3, t1, t2, t3]

/-- The cancellation step of `lem:multibound`: the multinomial term bound gives `M ≤ A^m`. -/
theorem multibound_of_term {M m : PTm k}
    (h : Γ ⊢[PRAAx] le (M * (pw (num 21) (num 21 * m) * pw (num 14) (num 14 * m) * pw (num 6) (num 6 * m)))
      (pw (num 42) (num 42 * m))) :
    Γ ⊢[PRAAx] le M (pw (num Aval) m) := by
  have hP : Γ ⊢[PRAAx] le one (pw (num 21) (num 21 * m) * pw (num 14) (num 14 * m) * pw (num 6) (num 6 * m)) := by
    have a := one_le_pw (Γ := Γ) (r := num 21) (by show Γ ⊢[PRAAx] le one (num 21); exact num_lt' 0 20) (num 21 * m)
    have b := one_le_pw (Γ := Γ) (r := num 14) (by exact num_lt' 0 13) (num 14 * m)
    have c := one_le_pw (Γ := Γ) (r := num 6) (by exact num_lt' 0 5) (num 6 * m)
    have ab := le_mul_mono (le_mul_mono a b) c
    ipra_le sl ab
  refine .orE (zero_or_succ (pw (num 21) (num 21 * m) * pw (num 14) (num 14 * m) * pw (num 6) (num 6 * m))) ?_ ?_
  · have h0 : ((pw (num 21) (num 21 * m) * pw (num 14) (num 14 * m) * pw (num 6) (num 6 * m) ≐ zero) :: Γ) ⊢[PRAAx]
        pw (num 21) (num 21 * m) * pw (num 14) (num 14 * m) * pw (num 6) (num 6 * m) ≐ zero := Prf.hyp0
    exact not_succ_le_self zero _ (le_congr (.eqRefl _) h0 hP.wk)
  · have eP := natEq (Prf.hyp0 : (((pw (num 21) (num 21 * m) * pw (num 14) (num 14 * m) * pw (num 6) (num 6 * m)) ≐ succ (pred (pw (num 21) (num 21 * m) * pw (num 14) (num 14 * m) * pw (num 6) (num 6 * m)))) :: Γ) ⊢[PRAAx] (pw (num 21) (num 21 * m) * pw (num 14) (num 14 * m) * pw (num 6) (num 6 * m)) ≐ succ (pred (pw (num 21) (num 21 * m) * pw (num 14) (num 14 * m) * pw (num 6) (num 6 * m))))
    have eI := natEq (power_identity (Γ := ((pw (num 21) (num 21 * m) * pw (num 14) (num 14 * m) * pw (num 6) (num 6 * m)) ≐ succ (pred (pw (num 21) (num 21 * m) * pw (num 14) (num 14 * m) * pw (num 6) (num 6 * m)))) :: Γ) m)
    have h' : (((pw (num 21) (num 21 * m) * pw (num 14) (num 14 * m) * pw (num 6) (num 6 * m)) ≐ succ (pred (pw (num 21) (num 21 * m) * pw (num 14) (num 14 * m) * pw (num 6) (num 6 * m)))) :: Γ) ⊢[PRAAx] le (M * (pw (num 21) (num 21 * m) * pw (num 14) (num 14 * m) * pw (num 6) (num 6 * m))) (pw (num 42) (num 42 * m)) := h.wk
    refine mul_le_cancel (d' := pred (pw (num 21) (num 21 * m) * pw (num 14) (num 14 * m) * pw (num 6) (num 6 * m))) ?_
    ipra_le sl h' using
      linear_combination -eI + (𝔞 M - 𝔞 (pw (num Aval) m)) * eP
where
  num_lt' (a b : ℕ) : Γ ⊢[PRAAx] le (one : PTm k) (num (b + 1)) := by
    refine le_of_eq_add (d := num b) ?_
    ipra_lc

end LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound

export_ipra DiophantineNumberTheory.AperyMultibound (mul_pw pw_num)
