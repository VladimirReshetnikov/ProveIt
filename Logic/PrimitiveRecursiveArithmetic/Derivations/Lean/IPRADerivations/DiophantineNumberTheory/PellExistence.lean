import IPRADerivations.DiophantineNumberTheory.PellSequence
import IPRADerivations.DiophantineNumberTheory.PellCollision
import IPRADerivations.Core.Pigeonhole

/-!
# Uniform bounded Pell existence

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/diophantine.tex`, `dio:pell-existence`:

  "For nonsquare `D ≥ 2`, define `C = 4D + 2`, `B = 4(D + 1)`, `K = 2C³`, `U = (B + 1)^{K+1}`,
  `H = 4(D + 1)²(U + 1)²`. There are integers `2 ≤ x ≤ H`, `1 ≤ y ≤ H`, `x² − D y² = 1`."

The proof follows the packet. The `K + 1` pairs `(p_i, q_i)`, `i ≤ K`, of `PellSequence` fall into fewer than `K`
classes (`PellSequence.cls_lt`), so the pigeonhole principle (`Core/Pigeonhole`) gives `i < j ≤ K` in one class:
equal sign of the norm, equal `a = |p² − D q²|` and equal residues modulo `a` (`PellSequence.split_eq`). Then
`PellCollision.collision_pos` or `collision_neg` gives `x² = D y² + 1` with `y ≥ 1`, and the sizes are bounded by
`p_k ≤ D U + 1`, `q_k ≤ U` (`PellSequence.T_pow`).

* `box`: the formula `∃x ∃y. 2 ≤ x ≤ H ∧ 1 ≤ y ≤ H ∧ x² = D y² + 1`; `box_intro`;
* `size_p`, `size_q`: `p_k ≤ D U + 1`, `q_k ≤ U` for `k ≤ K`;
* `two_le`: `x² = D y² + 1`, `y ≥ 1`, `D ≥ 2` give `x ≥ 2`;
* **`pell_existence`**.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.PellExistence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.PellApprox (Qv Cv pv qv pell_approx)
open LeanProofs.IPRA.DiophantineNumberTheory.PellSequence
open LeanProofs.IPRA.DiophantineNumberTheory.PellCollision (collision_pos collision_neg N1p N2p N1n N2n)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The constants and the statement -/

/-- `U = (B + 1)^{K+1}`. -/
abbrev Uv (D : PTm n) : PTm n := pw (B1 D) (succ (Kv D))

/-- `H = 4(D + 1)²(U + 1)²`. -/
abbrev Hv (D : PTm n) : PTm n := num 4 * (succ D * succ D) * (succ (Uv D) * succ (Uv D))

/-- The body `2 ≤ x ≤ H ∧ 1 ≤ y ≤ H ∧ x² = D y² + 1` over `x = var 1`, `y = var 0`. -/
abbrev boxBody (D H : PTm (n + 2)) : Fm PTm (n + 2) :=
  (le two (var 1) ⋏ le (var 1) H) ⋏ ((le one (var 0) ⋏ le (var 0) H) ⋏ (var 1 * var 1 ≐ D * (var 0 * var 0) + one))

/-- `∃x ∃y. 2 ≤ x ≤ H ∧ 1 ≤ y ≤ H ∧ x² = D y² + 1`. -/
abbrev box (D H : PTm n) : Fm PTm n :=
  Fm.ex (Fm.ex (boxBody (Syn.shift (Syn.shift D)) (Syn.shift (Syn.shift H))))

theorem sh2 (x H : PTm n) : Syn.subst (Syn.up (Syn.inst x)) (Syn.shift (Syn.shift H)) = Syn.shift H := by
  rw [Syn.subst_shift, Syn.subst_shift]
  first
  | simp [Syn.shift]
  | (simp; rfl)

theorem box_intro {D H x y : PTm n} (h : Γ ⊢[PRAAx] (le two x ⋏ le x H) ⋏ ((le one y ⋏ le y H) ⋏
    (x * x ≐ D * (y * y) + one))) : Γ ⊢[PRAAx] box D H := by
  refine .exI x (.exI y ?_)
  simpa [Fm.subst_and, Fm.subst_eq, subst_le, sh2, Syn.subst_inst_shift] using h

/-! ## Sizes -/

theorem add_one_mono {u v : PTm n} (h : Γ ⊢[PRAAx] le u v) : Γ ⊢[PRAAx] le (u + one) (v + one) := by
  ipra_le sl h

theorem sq_le_H (D U : PTm n) :
    Γ ⊢[PRAAx] le ((D * U + one) * (D * U + one)) (num 4 * (succ D * succ D) * (succ U * succ U)) := by
  ipra_le 3 * 𝔞 D * 𝔞 D * 𝔞 U * 𝔞 U + 8 * 𝔞 D * 𝔞 D * 𝔞 U + 8 * 𝔞 D * 𝔞 U * 𝔞 U + 4 * 𝔞 D * 𝔞 D +
    14 * 𝔞 D * 𝔞 U + 4 * 𝔞 U * 𝔞 U + 8 * 𝔞 D + 8 * 𝔞 U + 3

theorem prod_le_H {D U u v : PTm n} (h1 : Γ ⊢[PRAAx] le u (D * U + one)) (h2 : Γ ⊢[PRAAx] le v (D * U + one)) :
    Γ ⊢[PRAAx] le (u * v) (num 4 * (succ D * succ D) * (succ U * succ U)) :=
  le_trans (le_mul_mono h1 h2) (sq_le_H D U)

theorem U_le {D U : PTm n} (hD : Γ ⊢[PRAAx] le two D) : Γ ⊢[PRAAx] le U (D * U + one) := by
  ipra_le sl hD * 𝔞 U + 𝔞 U + 1

section Sizes

variable {D : PTm n} (hD : Γ ⊢[PRAAx] le two D) (hns : Γ ⊢[PRAAx] neg (D ≐ isqrt D * isqrt D))
include hD hns

theorem T_le_U {k : PTm n} (hk : Γ ⊢[PRAAx] le k (Kv D)) : Γ ⊢[PRAAx] le (T (succ k) D) (Uv D) :=
  le_trans (T_mono D ((succ_monus_succ _ _).eqTrans hk)) (le_trans (le_succ_self _) (T_pow _ D))

theorem size_q {k : PTm n} (hk : Γ ⊢[PRAAx] le k (Kv D)) : Γ ⊢[PRAAx] le (qS k D) (Uv D) :=
  le_trans (q_le hD hns k) (T_le_U hD hns hk)

theorem size_p {k : PTm n} (hk : Γ ⊢[PRAAx] le k (Kv D)) : Γ ⊢[PRAAx] le (pS k D) (D * Uv D + one) := by
  have a := Prf.andE₂ (Prf.andE₁ (Prf.andE₂ (pell_approx (Y := T k D) hD hns)))
  have hQ : Γ ⊢[PRAAx] le (Qv D (T k D)) (Uv D) := le_congr (T_succ k D) (.eqRefl _) (T_le_U hD hns hk)
  exact le_trans a (add_one_mono (le_mul_mono (le_refl D) hQ))

theorem size_q' {k : PTm n} (hk : Γ ⊢[PRAAx] le k (Kv D)) : Γ ⊢[PRAAx] le (qS k D) (D * Uv D + one) :=
  le_trans (size_q hD hns hk) (U_le hD)

theorem size_Dq {k : PTm n} (hk : Γ ⊢[PRAAx] le k (Kv D)) : Γ ⊢[PRAAx] le (D * qS k D) (D * Uv D + one) :=
  le_trans (le_mul_mono (le_refl D) (size_q hD hns hk)) (le_succ_self' _)
where
  le_succ_self' (t : PTm n) : Γ ⊢[PRAAx] le t (t + one) := le_add_right t one

end Sizes

theorem two_le {D x y : PTm n} (hD : Γ ⊢[PRAAx] le two D) (hy : Γ ⊢[PRAAx] le one y)
    (h : Γ ⊢[PRAAx] x * x ≐ D * (y * y) + one) : Γ ⊢[PRAAx] le two x := by
  refine .orE (lt_or_le x two) ?_ Prf.hyp0
  have hx : (lt x two :: Γ) ⊢[PRAAx] le x one := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have sq := le_mul_mono hx hx
  have e := natEq (h.wk (ψ := lt x two))
  have hD' := hD.wk (ψ := lt x two)
  have hy' := hy.wk (ψ := lt x two)
  have bad : (lt x two :: Γ) ⊢[PRAAx] le one zero := by
    ipra_le sl sq + sl hD' * (sl hy' * sl hy' + 2 * sl hy' + 1) + 2 * (sl hy' * sl hy' + 2 * sl hy') + 1 with e
  exact lt_zero_absurd _ bad

/-! ## The classes as a body -/

/-- The class of pair `i`, over `0 = i`, `1 = D`. -/
abbrev clsB : PTm 2 := cls (var 0) (var 1)

theorem low_lt {D : PTm n} (hD : Γ ⊢[PRAAx] le two D) (hns : Γ ⊢[PRAAx] neg (D ≐ isqrt D * isqrt D)) (k : PTm n) :
    Γ ⊢[PRAAx] lt (rem (pS k D) (A k D) * Cv D + rem (qS k D) (A k D)) (Cv D * Cv D) := by
  have Ap := A_pos hD hns k
  have Al := A_lt hD hns k
  have r1 := le_trans (rem_lt' Ap (pS k D)) (le_trans (le_succ_self _) Al)
  have r2 := le_trans (rem_lt' Ap (qS k D)) (le_trans (le_succ_self _) Al)
  ipra_le sl r1 * 𝔞 (Cv D) + sl r2

theorem C_pos (D : PTm n) : Γ ⊢[PRAAx] Cv D ≐ succ (pred (Cv D)) :=
  AnalyticNumberTheory.Primes.eq_succ_pred (y := succ (num 4 * D)) (by ipra_ring)

/-- The case where both norms have the sign `+`. -/
theorem finish_pos {D pi pj qi qj a : PTm n} (hD : Γ ⊢[PRAAx] le two D) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hi : Γ ⊢[PRAAx] pi * pi ≐ D * (qi * qi) + a) (hj : Γ ⊢[PRAAx] pj * pj ≐ D * (qj * qj) + a)
    (hp : Γ ⊢[PRAAx] rem pi a ≐ rem pj a) (hq : Γ ⊢[PRAAx] rem qi a ≐ rem qj a) (hlt : Γ ⊢[PRAAx] lt qi qj)
    {U : PTm n} (spi : Γ ⊢[PRAAx] le pi (D * U + one)) (spj : Γ ⊢[PRAAx] le pj (D * U + one))
    (sqj : Γ ⊢[PRAAx] le qj (D * U + one)) :
    Γ ⊢[PRAAx] box D (num 4 * (succ D * succ D) * (succ U * succ U)) := by
  have c := collision_pos ha hi hj hp hq hlt
  have y1 := Prf.andE₁ (Prf.andE₂ c)
  exact box_intro (.andI (.andI (two_le hD y1 (Prf.andE₁ c)) (le_trans (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ c)))
    (prod_le_H spi spj))) (.andI (.andI y1 (le_trans (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ c))) (prod_le_H spi sqj)))
    (Prf.andE₁ c)))

/-- The case where both norms have the sign `−`. -/
theorem finish_neg {D pi pj qi qj a : PTm n} (hD : Γ ⊢[PRAAx] le two D) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hi : Γ ⊢[PRAAx] D * (qi * qi) ≐ pi * pi + a) (hj : Γ ⊢[PRAAx] D * (qj * qj) ≐ pj * pj + a)
    (hp : Γ ⊢[PRAAx] rem pi a ≐ rem pj a) (hq : Γ ⊢[PRAAx] rem qi a ≐ rem qj a) (hlt : Γ ⊢[PRAAx] lt qi qj)
    {U : PTm n} (sDqi : Γ ⊢[PRAAx] le (D * qi) (D * U + one)) (sqi : Γ ⊢[PRAAx] le qi (D * U + one))
    (sqj : Γ ⊢[PRAAx] le qj (D * U + one)) (spj : Γ ⊢[PRAAx] le pj (D * U + one)) :
    Γ ⊢[PRAAx] box D (num 4 * (succ D * succ D) * (succ U * succ U)) := by
  have c := collision_neg ha hi hj hp hq hlt
  have y1 := Prf.andE₁ (Prf.andE₂ c)
  have hx : Γ ⊢[PRAAx] le (D * (qi * qj)) (num 4 * (succ D * succ D) * (succ U * succ U)) :=
    le_congr (by ipra_ring) (.eqRefl _) (prod_le_H sDqi sqj)
  exact box_intro (.andI (.andI (two_le hD y1 (Prf.andE₁ c)) (le_trans (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ c))) hx))
    (.andI (.andI y1 (le_trans (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ c))) (prod_le_H spj sqi))) (Prf.andE₁ c)))

/-! ## The theorem -/

/-- The `+` case of `norm_cases`. -/
abbrev NP (i D : PTm n) : Fm PTm n := (S i D ≐ zero) ⋏ (pS i D * pS i D ≐ D * (qS i D * qS i D) + A i D)

/-- The `−` case of `norm_cases`. -/
abbrev NN (i D : PTm n) : Fm PTm n := (S i D ≐ one) ⋏ (D * (qS i D * qS i D) ≐ pS i D * pS i D + A i D)

/-- **`dio:pell-existence`**: for nonsquare `D ≥ 2` there are `2 ≤ x ≤ H`, `1 ≤ y ≤ H` with `x² − D y² = 1`. -/
theorem pell_existence {D : PTm n} (hD : Γ ⊢[PRAAx] le two D) (hns : Γ ⊢[PRAAx] neg (D ≐ isqrt D * isqrt D)) :
    Γ ⊢[PRAAx] box D (Hv D) := by
  -- every class is below `K`
  have hr : Γ ⊢[PRAAx] Permutation.rangeAll clsB (Kv D) D := by
    refine .allI ?_
    have hD' : Γ.map Fm.shift ⊢[PRAAx] le two (Syn.shift D) := by simpa [Fm.shift, Syn.shift] using hD.shift
    have hns' : Γ.map Fm.shift ⊢[PRAAx] neg (Syn.shift D ≐ isqrt (Syn.shift D) * isqrt (Syn.shift D)) := by
      simpa [Fm.shift, Syn.shift] using hns.shift
    have e : inst2 clsB (var 0) (Syn.shift D) = cls (var 0) (Syn.shift D) := by simp [inst2]
    have sK : Syn.shift (Kv D) = Kv (Syn.shift D) := by simp [Syn.shift]
    rw [e, sK]
    exact cls_lt hD' hns' _
  have ph := Pigeonhole.pigeonhole (S := clsB) hr
  have hij := Prf.andE₁ ph
  have hjK := Prf.andE₁ (Prf.andE₂ ph)
  have hc0 := Prf.andE₂ (Prf.andE₂ ph)
  have ei : ∀ k : PTm n, inst2 clsB k D = cls k D := fun k => by simp [inst2]
  rw [ei, ei] at hc0
  let i := Pigeonhole.phpI clsB (Kv D) D
  let j := Pigeonhole.phpJ clsB (Kv D) D
  have hiK : Γ ⊢[PRAAx] le i (Kv D) := le_trans (le_succ_self _) (le_trans hij hjK)
  -- decoding the common class
  have CC : Γ ⊢[PRAAx] Cv D * Cv D ≐ succ (pred (Cv D * Cv D)) := Combinatorics.Binomial.pos_mul (C_pos D) (C_pos D)
  have s1 := split_eq CC (low_lt hD hns i) (low_lt hD hns j) hc0
  have s2 := split_eq (C_pos D) (A_lt hD hns i) (A_lt hD hns j) (Prf.andE₁ s1)
  have eA : Γ ⊢[PRAAx] A j D ≐ A i D := (Prf.andE₂ s2).eqSymm
  have r1 := le_trans (rem_lt' (A_pos hD hns i) (qS i D)) (le_trans (le_succ_self _) (A_lt hD hns i))
  have r2 := le_trans (rem_lt' (A_pos hD hns j) (qS j D)) (le_trans (le_succ_self _) (A_lt hD hns j))
  have s3 := split_eq (C_pos D) r1 r2 (Prf.andE₂ s1)
  have hp : Γ ⊢[PRAAx] rem (pS i D) (A i D) ≐ rem (pS j D) (A i D) :=
    (Prf.andE₁ s3).eqTrans (congrAp2 remF (.eqRefl _) eA)
  have hq : Γ ⊢[PRAAx] rem (qS i D) (A i D) ≐ rem (qS j D) (A i D) :=
    (Prf.andE₂ s3).eqTrans (congrAp2 remF (.eqRefl _) eA)
  have hlt := q_lt hD hns hij
  have ha := A_pos hD hns i
  have eS := Prf.andE₁ s2
  have U' : Γ ⊢[PRAAx] Hv D ≐ num 4 * (succ D * succ D) * (succ (Uv D) * succ (Uv D)) := .eqRefl _
  refine .orE (norm_cases i D) ?_ ?_
  · refine .orE (norm_cases j D) ?_ ?_
    · have hi : (NP j D :: NP i D :: Γ) ⊢[PRAAx] pS i D * pS i D ≐ D * (qS i D * qS i D) + A i D :=
        Prf.andE₂ Prf.hyp1
      have hj0 : (NP j D :: NP i D :: Γ) ⊢[PRAAx] pS j D * pS j D ≐ D * (qS j D * qS j D) + A j D :=
        Prf.andE₂ Prf.hyp0
      have hj := hj0.eqTrans (congrAdd (.eqRefl _) eA.wk.wk)
      exact finish_pos hD.wk.wk ha.wk.wk hi hj hp.wk.wk hq.wk.wk hlt.wk.wk
        (size_p hD.wk.wk hns.wk.wk hiK.wk.wk) (size_p hD.wk.wk hns.wk.wk hjK.wk.wk)
        (size_q' hD.wk.wk hns.wk.wk hjK.wk.wk)
    · have s0 : (NN j D :: NP i D :: Γ) ⊢[PRAAx] S i D ≐ zero := Prf.andE₁ Prf.hyp1
      have s1' : (NN j D :: NP i D :: Γ) ⊢[PRAAx] S j D ≐ one := Prf.andE₁ Prf.hyp0
      exact .botE _ (succ_ne_zero (a := zero) (s1'.eqSymm.eqTrans (eS.wk.wk.eqSymm.eqTrans s0)))
  · refine .orE (norm_cases j D) ?_ ?_
    · have s1' : (NP j D :: NN i D :: Γ) ⊢[PRAAx] S i D ≐ one := Prf.andE₁ Prf.hyp1
      have s0 : (NP j D :: NN i D :: Γ) ⊢[PRAAx] S j D ≐ zero := Prf.andE₁ Prf.hyp0
      exact .botE _ (succ_ne_zero (a := zero) (s1'.eqSymm.eqTrans (eS.wk.wk.eqTrans s0)))
    · have hi : (NN j D :: NN i D :: Γ) ⊢[PRAAx] D * (qS i D * qS i D) ≐ pS i D * pS i D + A i D :=
        Prf.andE₂ Prf.hyp1
      have hj0 : (NN j D :: NN i D :: Γ) ⊢[PRAAx] D * (qS j D * qS j D) ≐ pS j D * pS j D + A j D :=
        Prf.andE₂ Prf.hyp0
      have hj := hj0.eqTrans (congrAdd (.eqRefl _) eA.wk.wk)
      exact finish_neg hD.wk.wk ha.wk.wk hi hj hp.wk.wk hq.wk.wk hlt.wk.wk
        (size_Dq hD.wk.wk hns.wk.wk hiK.wk.wk) (size_q' hD.wk.wk hns.wk.wk hiK.wk.wk)
        (size_q' hD.wk.wk hns.wk.wk hjK.wk.wk) (size_p hD.wk.wk hns.wk.wk hjK.wk.wk)

end LeanProofs.IPRA.DiophantineNumberTheory.PellExistence
