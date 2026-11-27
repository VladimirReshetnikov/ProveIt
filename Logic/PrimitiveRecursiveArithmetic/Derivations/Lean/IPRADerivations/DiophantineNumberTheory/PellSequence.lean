import IPRADerivations.DiophantineNumberTheory.PellApprox
import IPRADerivations.AnalyticNumberTheory.PrimorialUpper

/-!
# The sequence of approximations and its classes

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/diophantine.tex`, the construction in the
proof of `dio:pell-existence`: "Let `T_0 = 0`, `T_{i+1} = B(T_i + 1)`. For each `i = 0, …, K` use the preceding lemma
with `Y = T_i` to obtain `(p_i, q_i)` and `m_i = p_i² − D q_i²` … The `q_i` strictly increase. Induction gives
`T_i + 1 ≤ (B + 1)^i` … Classify a pair by `(m_i, p_i mod |m_i|, q_i mod |m_i|)`. There are at most `2C³ = K`
classes: use a sign-and-magnitude tag less than `2C`, and two residue slots each less than `C`."

* `T`, `T_zero`, `T_succ` (`T_{i+1} = Q(T_i) = 4(D+1)(T_i + 1)`), `T_lt_succ`, `T_mono`, `T_pow` (`T_i + 1 ≤ (B+1)^i`);
* `pS i`, `qS i`: the pair of `PellApprox.pell_approx` at `Y = T_i`; **`q_lt`**: `q_i < q_j` for `i < j`;
* `A i = |p_i² − D q_i²|`, `S i = [p_i² < D q_i²]`, `A_pos`, `A_lt` (`1 ≤ A < C`);
* `cls i = (S C + A)·C² + (p_i mod A)·C + (q_i mod A)`; **`cls_lt`**: `cls i < 2C³`;
* **`decode`**: equal classes have equal sign bits, magnitudes and residues.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.PellSequence

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.PellApprox (Qv Cv pv qv Q_pos pell_approx)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dmu)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The sequence `T` -/

/-- Step variables: `0 = i`, `1 = T_i`, `2 = D`. -/
def stepT : PTm 3 := num 4 * (succ (var 2) * succ (var 1))

abbrev T (i D : PTm n) : PTm n := ap2 (rec2 zero stepT) i D

theorem T_zero (D : PTm n) : Γ ⊢[PRAAx] T zero D ≐ zero := by
  have h := rec2_zero (Γ := Γ) zero stepT D
  simpa using h

theorem T_succ (i D : PTm n) : Γ ⊢[PRAAx] T (succ i) D ≐ Qv D (T i D) := by
  have h := rec2_succ (Γ := Γ) zero stepT i D
  have e : Syn.subst ![i, ap2 (rec2 zero stepT) i D, D] stepT = Qv D (ap2 (rec2 zero stepT) i D) := by
    simp [stepT]
  rw [e] at h; exact h

theorem T_lt_succ (i D : PTm n) : Γ ⊢[PRAAx] lt (T i D) (T (succ i) D) := by
  have e := natEq (T_succ (Γ := Γ) i D)
  ipra_le 4 * 𝔞 D * 𝔞 (T i D) + 4 * 𝔞 D + 3 * 𝔞 (T i D) + 3 with e

theorem T_mono_add (i D : PTm n) (d : PTm n) : Γ ⊢[PRAAx] le (T i D) (T (i + d) D) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (T (Syn.shift i) (Syn.shift D)) (T (Syn.shift i + var 0) (Syn.shift D))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero]
      exact le_congr (.eqRefl _) (congrAp2 _ (add_zero i).eqSymm (.eqRefl _)) (le_refl _)
    · simp only [subst_le, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine le_trans Prf.hyp0 (le_congr (.eqRefl _) (congrAp2 _ (add_succ _ _).eqSymm (.eqRefl _)) ?_)
      exact le_trans (le_succ_self _) (T_lt_succ _ _)
  have h2 := Prf.allE d hall
  simp only [subst_le, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero] at h2
  exact h2

theorem T_mono {i j : PTm n} (D : PTm n) (h : Γ ⊢[PRAAx] le i j) : Γ ⊢[PRAAx] le (T i D) (T j D) :=
  le_congr (.eqRefl _) (congrAp2 _ (eq_add_of_le h).eqSymm (.eqRefl _)) (T_mono_add i D (monus j i))

/-- `B + 1 = 4(D + 1) + 1`. -/
abbrev B1 (D : PTm n) : PTm n := succ (num 4 * succ D)

theorem pow_step {D Ti Ti1 P P1 : PTm n} (ih : Γ ⊢[PRAAx] le (succ Ti) P) (e1 : Γ ⊢[PRAAx] Ti1 ≐ Qv D Ti)
    (e2 : Γ ⊢[PRAAx] P1 ≐ P * B1 D) : Γ ⊢[PRAAx] le (succ Ti1) P1 := by
  have x := natEq e1; have y := natEq e2
  ipra_le (4 * 𝔞 D + 5) * sl ih + 𝔞 Ti with x - y

/-- **`T_i + 1 ≤ (B + 1)^i`.** -/
theorem T_pow (i D : PTm n) : Γ ⊢[PRAAx] le (succ (T i D)) (pw (B1 D) i) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (succ (T (var 0) (Syn.shift D))) (pw (B1 (Syn.shift D)) (var 0))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ, PTm.subst_num]
      exact le_congr (congrSucc (T_zero D)).eqSymm (pw_zero _).eqSymm (le_refl _)
    · simp only [subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ, PTm.subst_num]
      exact pow_step Prf.hyp0 (T_succ _ _) (pw_succ _ _)
  have h2 := Prf.allE i hall
  simp only [subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ, PTm.subst_num] at h2
  exact h2

/-! ## The pairs -/

abbrev pS (i D : PTm n) : PTm n := pv D (T i D)
abbrev qS (i D : PTm n) : PTm n := qv D (T i D)

section Pairs

variable {D : PTm n} (hD : Γ ⊢[PRAAx] le two D) (hns : Γ ⊢[PRAAx] neg (D ≐ isqrt D * isqrt D))
include hD hns

theorem q_gt (i : PTm n) : Γ ⊢[PRAAx] lt (T i D) (qS i D) := Prf.andE₁ (Prf.andE₁ (pell_approx (Y := T i D) hD hns))

theorem q_le (i : PTm n) : Γ ⊢[PRAAx] le (qS i D) (T (succ i) D) :=
  le_congr (.eqRefl _) (T_succ i D).eqSymm (Prf.andE₂ (Prf.andE₁ (pell_approx (Y := T i D) hD hns)))

/-- **The denominators strictly increase.** -/
theorem q_lt {i j : PTm n} (hij : Γ ⊢[PRAAx] lt i j) : Γ ⊢[PRAAx] lt (qS i D) (qS j D) :=
  le_trans ((succ_monus_succ _ _).eqTrans (le_trans (q_le hD hns i) (T_mono D hij))) (q_gt hD hns j)

end Pairs

/-! ## Norms and classes -/

/-- `|p² − D q²|`. -/
abbrev A (i D : PTm n) : PTm n :=
  monus (pS i D * pS i D) (D * (qS i D * qS i D)) + monus (D * (qS i D * qS i D)) (pS i D * pS i D)

/-- The sign bit `[p² < D q²]`. -/
abbrev S (i D : PTm n) : PTm n := sg (monus (D * (qS i D * qS i D)) (pS i D * pS i D))

/-- `cls i = (S C + A) C² + (p mod A) C + (q mod A)`. -/
abbrev cls (i D : PTm n) : PTm n :=
  (S i D * Cv D + A i D) * (Cv D * Cv D) + (rem (pS i D) (A i D) * Cv D + rem (qS i D) (A i D))

/-- The number of classes `K = 2C³`. -/
abbrev Kv (D : PTm n) : PTm n := two * (Cv D * (Cv D * Cv D))

/-- The two cases of the norm: `p² = Dq² + A` with `S = 0`, or `Dq² = p² + A` with `S = 1`. -/
theorem norm_cases (i D : PTm n) :
    Γ ⊢[PRAAx] ((S i D ≐ zero) ⋏ (pS i D * pS i D ≐ D * (qS i D * qS i D) + A i D)) ⋎
      ((S i D ≐ one) ⋏ (D * (qS i D * qS i D) ≐ pS i D * pS i D + A i D)) := by
  refine .orE (zero_or_succ (monus (D * (qS i D * qS i D)) (pS i D * pS i D))) ?_ ?_
  · refine .orI₁ (.andI ((congrSg Prf.hyp0).eqTrans sg_zero) ?_)
    have h0 : ((monus (D * (qS i D * qS i D)) (pS i D * pS i D) ≐ zero) :: Γ) ⊢[PRAAx]
        le (D * (qS i D * qS i D)) (pS i D * pS i D) := Prf.hyp0
    have e := natEq (eq_add_of_le h0)
    ipra_lc e - natEq (Prf.hyp0 : ((monus (D * (qS i D * qS i D)) (pS i D * pS i D) ≐ zero) :: Γ) ⊢[PRAAx] _ ≐ _)
  · refine .orI₂ (.andI ((congrSg Prf.hyp0).eqTrans (sg_succ _)) ?_)
    have hs : ((monus (D * (qS i D * qS i D)) (pS i D * pS i D) ≐
        succ (pred (monus (D * (qS i D * qS i D)) (pS i D * pS i D)))) :: Γ) ⊢[PRAAx]
        le (pS i D * pS i D) (D * (qS i D * qS i D)) := by
      refine .orE (lt_or_le (pS i D * pS i D) (D * (qS i D * qS i D))) (le_trans (le_succ_self _) Prf.hyp0) ?_
      exact .botE _ (succ_ne_zero (a := pred _) (Prf.hyp1.eqSymm.eqTrans Prf.hyp0))
    have e := natEq (eq_add_of_le hs)
    ipra_lc e - natEq (hs : _ ⊢[PRAAx] monus (pS i D * pS i D) (D * (qS i D * qS i D)) ≐ zero)

theorem A_lt_pos {P Q C A : PTm n} (h : Γ ⊢[PRAAx] lt P (Q + C)) (e : Γ ⊢[PRAAx] P ≐ Q + A) :
    Γ ⊢[PRAAx] lt A C := by
  have x := natEq e
  ipra_le sl h with x

theorem A_lt_neg {P Q C A : PTm n} (h : Γ ⊢[PRAAx] lt Q (P + C)) (e : Γ ⊢[PRAAx] Q ≐ P + A) :
    Γ ⊢[PRAAx] lt A C := by
  have x := natEq e
  ipra_le sl h with x

section Bounds

variable {D : PTm n} (hD : Γ ⊢[PRAAx] le two D) (hns : Γ ⊢[PRAAx] neg (D ≐ isqrt D * isqrt D))
include hD hns

theorem A_pos (i : PTm n) : Γ ⊢[PRAAx] A i D ≐ succ (pred (A i D)) := by
  have ne := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (pell_approx (Y := T i D) hD hns)))
  refine .orE (zero_or_succ (A i D)) ?_ Prf.hyp0
  refine .botE _ (.impE ne.wk ?_)
  refine .orE (norm_cases (Γ := (A i D ≐ zero) :: Γ) i D) ?_ ?_
  · exact (Prf.andE₂ Prf.hyp0).eqTrans ((congrAdd (.eqRefl _) Prf.hyp1).eqTrans (add_zero _))
  · exact ((Prf.andE₂ Prf.hyp0).eqTrans ((congrAdd (.eqRefl _) Prf.hyp1).eqTrans (add_zero _))).eqSymm

theorem A_lt (i : PTm n) : Γ ⊢[PRAAx] lt (A i D) (Cv D) := by
  have nb := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (pell_approx (Y := T i D) hD hns)))
  exact .orE (norm_cases i D) (A_lt_pos (Prf.andE₁ nb).wk (Prf.andE₂ Prf.hyp0))
    (A_lt_neg (Prf.andE₂ nb).wk (Prf.andE₂ Prf.hyp0))

theorem cls_alg {S C A rp rq : PTm n} (hS : Γ ⊢[PRAAx] le S one) (hA : Γ ⊢[PRAAx] lt A C)
    (hp : Γ ⊢[PRAAx] lt rp C) (hq : Γ ⊢[PRAAx] lt rq C) :
    Γ ⊢[PRAAx] lt ((S * C + A) * (C * C) + (rp * C + rq)) (two * (C * (C * C))) := by
  ipra_le sl hS * 𝔞 C * 𝔞 C * 𝔞 C + sl hA * 𝔞 C * 𝔞 C + sl hp * 𝔞 C + sl hq

/-- **`cls i < 2C³`.** -/
theorem cls_lt (i : PTm n) : Γ ⊢[PRAAx] lt (cls i D) (Kv D) := by
  have Ap := A_pos hD hns i
  have Al := A_lt hD hns i
  exact cls_alg hD hns (sg_le1 _) Al (le_trans (rem_lt' Ap _) (le_trans (le_succ_self _) Al))
    (le_trans (rem_lt' Ap _) (le_trans (le_succ_self _) Al))

end Bounds

/-! ## Decoding -/

theorem split_eq {M u v u' v' : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hv : Γ ⊢[PRAAx] lt v M)
    (hv' : Γ ⊢[PRAAx] lt v' M) (h : Γ ⊢[PRAAx] u * M + v ≐ u' * M + v') :
    Γ ⊢[PRAAx] (u ≐ u') ⋏ (v ≐ v') := by
  have d1 := dmu (z := u * M + v) (q := u) (r := v) hM (by ipra_ring) hv
  have d2 := dmu (z := u' * M + v') (q := u') (r := v') hM (by ipra_ring) hv'
  exact .andI ((Prf.andE₁ d1).eqSymm.eqTrans ((congrAp2 quoF h (.eqRefl _)).eqTrans (Prf.andE₁ d2)))
    ((Prf.andE₂ d1).eqSymm.eqTrans ((congrAp2 remF h (.eqRefl _)).eqTrans (Prf.andE₂ d2)))

end LeanProofs.IPRA.DiophantineNumberTheory.PellSequence
