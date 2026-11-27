import IPRADerivations.Analysis.Polynomials.Evaluation.Bounds.PolynomialLipschitz
import IPRADerivations.Analysis.RationalArithmetic.Powers.PowerIncrement

/-!
# The second-order Taylor estimate of a polynomial

Packets: `foundations/ipra_local_global`, `paper/04_ode.tex`, the finite remainder estimate
`eq:ode-polyremainder`, `|H(x + v) − H(x) − ∇H(x) · v| ≤ R_H ‖v‖²` (one variable here); `analysis/calculus_ipra`,
the monomial remainder `eq:monomialremainder` summed over a polynomial.

For natural coefficients `c(j, x)`, a point `a` and an increment `h` (cleared rationals), with
`P(a) = ∑_{j<D} c_j a^j`, the derivative term `P′(a) = ∑ c_j j a^{j−1}` (`PolynomialLipschitz.lipB`) and the
second-order majorant `Q(R) = ∑ c_j (j − 1) j R^{j−1}`:

* `d2B`, `d2_at`: the terms of `Q(R)`;
* `term_lower`, `term_upper`: one monomial, `c_j a^j + h c_j j a^{j−1} ≤ c_j (a + h)^j` and, for `a + h ≤ R`,
  `2R c_j (a + h)^j ≤ 2R (c_j a^j + h c_j j a^{j−1}) + h² c_j (j − 1) j R^{j−1}` (`PowerIncrement`; `j = 0` is
  constant);
* `taylor_lower`: `P(a) + h P′(a) ≤ P(a + h)`;
* `taylor_upper`: `2R P(a + h) ≤ 2R (P(a) + h P′(a)) + h² Q(R)`,

so `0 ≤ P(a + h) − P(a) − h P′(a) ≤ h² Q(R)/(2R)`, the remainder estimate with an explicit constant. Both are
quantifier-free inductions on the number of coefficients.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.PolynomialTaylor

open_ipra
open LeanProofs.IPRA.Analysis.PolynomialLipschitz (polyB lipB poly_at lip_at)
open LeanProofs.IPRA.Analysis.PowerIncrement (power_inc_lower power_inc_upper)
open LeanProofs.IPRA.Analysis.PowerGap (shift_le')
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

section Taylor

variable (c : PTm 2)

/-- `c_j (j − 1) j R^{j−1}` over `0 = j`, `1 = ⟨R, x⟩`. -/
def d2B : PTm 2 :=
  Syn.subst ![Syn.var 0, sndT (Syn.var 1)] c * (pred (Syn.var 0) * Syn.var 0 * pw (fstT (Syn.var 1)) (pred (Syn.var 0)))

theorem inst2_d2B (j y : PTm n) :
    inst2 (d2B c) j y = inst2 c j (sndT y) * (pred j * j * pw (fstT y) (pred j)) := by
  simp only [d2B, inst2, Syn.subst_subst, subst_vecCons, subst_vecEmpty,
    subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    PTm.subst_mul, PTm.subst_pred, subst_ap2]

theorem d2_at (j R x : PTm n) :
    Γ ⊢[PRAAx] inst2 (d2B c) j (pairT R x) ≐ inst2 c j x * (pred j * j * pw R (pred j)) := by
  rw [inst2_d2B]
  exact congrMul (congrInst2 c (.eqRefl _) (snd_pair _ _))
    (congrMul (.eqRefl _) (congrPw (fst_pair _ _) (.eqRefl _)))

variable {c}

/-- One monomial, lower: `c a^j + h c j a^{j−1} ≤ c (a + h)^j`. -/
theorem term_lower {x a h : PTm n} (j : PTm n) :
    Γ ⊢[PRAAx] le (inst2 c j x * pw a j + h * (inst2 c j x * (j * pw a (pred j))))
      (inst2 c j x * pw (a + h) j) := by
  refine .orE (zero_or_succ j) ?_ ?_
  · have hj : ((j ≐ zero) :: Γ) ⊢[PRAAx] j ≐ zero := Prf.hyp0
    have ej := natEq hj
    have e1 := natEq ((congrPw (.eqRefl a) hj).eqTrans (pw_zero a))
    have e2 := natEq ((congrPw (.eqRefl (a + h)) hj).eqTrans (pw_zero (a + h)))
    ipra_le 0 using
      linear_combination 𝔟 (inst2 c j x) * e2 - 𝔟 (inst2 c j x) * e1 -
        𝔟 h * 𝔟 (inst2 c j x) * 𝔟 (pw a (pred j)) * ej
  · have hj : ((j ≐ succ (pred j)) :: Γ) ⊢[PRAAx] j ≐ succ (pred j) := Prf.hyp0
    have pl := power_inc_lower (Γ := (j ≐ succ (pred j)) :: Γ) a h (pred j)
    have pl' : ((j ≐ succ (pred j)) :: Γ) ⊢[PRAAx]
        le (pw a j + j * pw a (pred j) * h) (pw (a + h) j) :=
      le_congr (congrAdd (congrPw (.eqRefl a) hj.eqSymm) (congrMul (congrMul hj.eqSymm (.eqRefl _)) (.eqRefl h)))
        (congrPw (.eqRefl _) hj.eqSymm) pl
    ipra_le 𝔟 (inst2 c j x) * sl pl'

/-- One monomial, upper, for `a + h ≤ R`. -/
theorem term_upper {x a h R : PTm n} (hR : Γ ⊢[PRAAx] le (a + h) R) (j : PTm n) :
    Γ ⊢[PRAAx] le (two * R * (inst2 c j x * pw (a + h) j))
      (two * R * (inst2 c j x * pw a j + h * (inst2 c j x * (j * pw a (pred j)))) +
        h * h * (inst2 c j x * (pred j * j * pw R (pred j)))) := by
  refine .orE (zero_or_succ j) ?_ ?_
  · have hj : ((j ≐ zero) :: Γ) ⊢[PRAAx] j ≐ zero := Prf.hyp0
    have ej := natEq hj
    have e1 := natEq ((congrPw (.eqRefl a) hj).eqTrans (pw_zero a))
    have e2 := natEq ((congrPw (.eqRefl (a + h)) hj).eqTrans (pw_zero (a + h)))
    ipra_le 0 using
      linear_combination 2 * 𝔟 R * 𝔟 (inst2 c j x) * e1 - 2 * 𝔟 R * 𝔟 (inst2 c j x) * e2 +
        (2 * 𝔟 R * 𝔟 h * 𝔟 (inst2 c j x) * 𝔟 (pw a (pred j)) +
          𝔟 h * 𝔟 h * 𝔟 (inst2 c j x) * 𝔟 (pred j) * 𝔟 (pw R (pred j))) * ej
  · have hj : ((j ≐ succ (pred j)) :: Γ) ⊢[PRAAx] j ≐ succ (pred j) := Prf.hyp0
    have pu := power_inc_upper (Γ := (j ≐ succ (pred j)) :: Γ) (pred j) hR.wk
    have pu' : ((j ≐ succ (pred j)) :: Γ) ⊢[PRAAx]
        le (two * R * pw (a + h) j)
          (two * R * (pw a j + j * pw a (pred j) * h) + pred j * j * pw R (pred j) * (h * h)) :=
      le_congr (congrMul (.eqRefl _) (congrPw (.eqRefl _) hj.eqSymm))
        (congrAdd (congrMul (.eqRefl _) (congrAdd (congrPw (.eqRefl a) hj.eqSymm)
          (congrMul (congrMul hj.eqSymm (.eqRefl _)) (.eqRefl h))))
          (congrMul (congrMul (congrMul (.eqRefl _) hj.eqSymm) (.eqRefl _)) (.eqRefl _))) pu
    ipra_le 𝔟 (inst2 c j x) * sl pu'

/-! ## The polynomial -/

/-- `P(a) + h P′(a) ≤ P(a + h)` for the first `D` coefficients. -/
abbrev LowInv (c : PTm 2) (D a h x : PTm n) : Fm PTm n :=
  le (ap2 (sumF (polyB c)) D (pairT a x) + h * ap2 (sumF (lipB c)) D (pairT a x))
    (ap2 (sumF (polyB c)) D (pairT (a + h) x))

/-- `2R P(a + h) ≤ 2R (P(a) + h P′(a)) + h² Q(R)` for the first `D` coefficients. -/
abbrev UpInv (c : PTm 2) (D a h R x : PTm n) : Fm PTm n :=
  le (two * R * ap2 (sumF (polyB c)) D (pairT (a + h) x))
    (two * R * (ap2 (sumF (polyB c)) D (pairT a x) + h * ap2 (sumF (lipB c)) D (pairT a x)) +
      h * h * ap2 (sumF (d2B c)) D (pairT R x))

theorem low_step {D a h x : PTm n} (ih : Γ ⊢[PRAAx] LowInv c D a h x) :
    Γ ⊢[PRAAx] LowInv c (succ D) a h x := by
  have e1 := natEq (sum_succ' (Γ := Γ) (polyB c) D (pairT a x))
  have e2 := natEq (sum_succ' (Γ := Γ) (lipB c) D (pairT a x))
  have e3 := natEq (sum_succ' (Γ := Γ) (polyB c) D (pairT (a + h) x))
  have a1 := natEq (poly_at (Γ := Γ) c D a x)
  have a2 := natEq (lip_at (Γ := Γ) c D a x)
  have a3 := natEq (poly_at (Γ := Γ) c D (a + h) x)
  have t := term_lower (c := c) (x := x) (a := a) (h := h) (Γ := Γ) D
  ipra_le sl ih + sl t using rw [e1, e2, e3, a1, a2, a3]; ring

theorem up_step {D a h R x : PTm n} (hR : Γ ⊢[PRAAx] le (a + h) R) (ih : Γ ⊢[PRAAx] UpInv c D a h R x) :
    Γ ⊢[PRAAx] UpInv c (succ D) a h R x := by
  have e1 := natEq (sum_succ' (Γ := Γ) (polyB c) D (pairT a x))
  have e2 := natEq (sum_succ' (Γ := Γ) (lipB c) D (pairT a x))
  have e3 := natEq (sum_succ' (Γ := Γ) (polyB c) D (pairT (a + h) x))
  have e4 := natEq (sum_succ' (Γ := Γ) (d2B c) D (pairT R x))
  have a1 := natEq (poly_at (Γ := Γ) c D a x)
  have a2 := natEq (lip_at (Γ := Γ) c D a x)
  have a3 := natEq (poly_at (Γ := Γ) c D (a + h) x)
  have a4 := natEq (d2_at (Γ := Γ) c D R x)
  have t := term_upper (c := c) (x := x) hR D
  ipra_le sl ih + sl t using rw [e1, e2, e3, e4, a1, a2, a3, a4]; ring

/-- `P(a) + h P′(a) ≤ P(a + h)`. -/
theorem taylor_lower (a h x D : PTm n) : Γ ⊢[PRAAx] LowInv c D a h x := by
  have hall : Γ ⊢[PRAAx] Fm.all (LowInv c (Syn.var 0) (Syn.shift a) (Syn.shift h) (Syn.shift x)) := by
    ipra_qfind (le_QF _ _) [subst_le, subst_ap2, subst_pairT]
    · have z1 := natEq (sum_zero (Γ := Γ) (polyB c) (pairT a x))
      have z2 := natEq (sum_zero (Γ := Γ) (lipB c) (pairT a x))
      have z3 := natEq (sum_zero (Γ := Γ) (polyB c) (pairT (a + h) x))
      ipra_le 0 using rw [z1, z2, z3]; ring
    · exact low_step Prf.hyp0
  have h2 := Prf.allE D hall
  simpa only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] using h2

/-- `2R P(a + h) ≤ 2R (P(a) + h P′(a)) + h² Q(R)` for `a + h ≤ R`. -/
theorem taylor_upper {a h R x : PTm n} (hR : Γ ⊢[PRAAx] le (a + h) R) (D : PTm n) :
    Γ ⊢[PRAAx] UpInv c D a h R x := by
  have hall : Γ ⊢[PRAAx] Fm.all (UpInv c (Syn.var 0) (Syn.shift a) (Syn.shift h) (Syn.shift R)
      (Syn.shift x)) := by
    ipra_qfind (le_QF _ _) [subst_le, subst_ap2, subst_pairT]
    · have z1 := natEq (sum_zero (Γ := Γ) (polyB c) (pairT a x))
      have z2 := natEq (sum_zero (Γ := Γ) (lipB c) (pairT a x))
      have z3 := natEq (sum_zero (Γ := Γ) (polyB c) (pairT (a + h) x))
      have z4 := natEq (sum_zero (Γ := Γ) (d2B c) (pairT R x))
      ipra_le 0 using rw [z1, z2, z3, z4]; ring
    · have hR' := shift_le' hR
      have e : Syn.shift (a + h) = Syn.shift a + Syn.shift h := by simp [Syn.shift]
      rw [e] at hR'
      exact up_step hR'.wk Prf.hyp0
  have h2 := Prf.allE D hall
  simpa only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] using h2

end Taylor

end LeanProofs.IPRA.Analysis.PolynomialTaylor
