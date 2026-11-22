import IPRADerivations.DiophantineNumberTheory.ZTCancel
import IPRADerivations.DiophantineNumberTheory.ConicLower

/-!
# `L` and `R` have no common projective zero

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Section `sec:conics`: "If `L(s, t) = R(s, t) = 0`,
these identities and `r ≠ 0` imply `s = t = 0`. Thus `L` and `R` have no common projective zero over `ℚ`; this
conclusion has been obtained without a resultant theorem." It is used in `thm:conic-param` ("If `L(s, t) = 0`, then
`R(s, t) ≠ 0`").

* `zt_dec`: an integer term is `0` or not (decidable natural equality of its parts);
* `zt_sq_zero`: `s² = 0` gives `s = 0`;
* `no_common_zero`: `L(s, t) = R(s, t) = 0` and `r ≠ 0` give `s = t = 0` (from `identity_s`, `identity_t` and
  `ZTCancel.zt_no_zero_div`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.ConicNonzero

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.ConicIdentities (Form)
open LeanProofs.IPRA.DiophantineNumberTheory.ZTCancel (zt_no_zero_div)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- An integer term is `0` or not. -/
theorem zt_dec (s : ZT n) : Γ ⊢[PRAAx] ZT.eq s (ZT.natLit 0) ⋎ neg (ZT.eq s (ZT.natLit 0)) := by
  refine .orE (lt_or_le s.neg s.pos) ?_ ?_
  · refine .orI₂ (.impI ?_)
    have hl : (ZT.eq s (ZT.natLit 0) :: lt s.neg s.pos :: Γ) ⊢[PRAAx] le (succ s.neg) s.pos := Prf.hyp1
    have e : (ZT.eq s (ZT.natLit 0) :: lt s.neg s.pos :: Γ) ⊢[PRAAx] s.pos + zero ≐ num 0 + s.neg := Prf.hyp0
    have e' := natEq e
    exact not_succ_le_self s.neg _ (le_congr (.eqRefl _) (by apply deriveNat; ipra_simps; linear_combination e') hl)
  · refine .orE (lt_or_le s.pos s.neg) ?_ ?_
    · refine .orI₂ (.impI ?_)
      have hl : (ZT.eq s (ZT.natLit 0) :: lt s.pos s.neg :: le s.pos s.neg :: Γ) ⊢[PRAAx] le (succ s.pos) s.neg := Prf.hyp1
      have e : (ZT.eq s (ZT.natLit 0) :: lt s.pos s.neg :: le s.pos s.neg :: Γ) ⊢[PRAAx] s.pos + zero ≐ num 0 + s.neg :=
        Prf.hyp0
      have e' := natEq e
      exact not_succ_le_self s.pos _ (le_congr (.eqRefl _) (by apply deriveNat; ipra_simps; linear_combination -e') hl)
    · refine .orI₁ ?_
      have eq := le_antisymm (Prf.hyp0 : (le s.neg s.pos :: le s.pos s.neg :: Γ) ⊢[PRAAx] le s.neg s.pos)
        (Prf.hyp1 : (le s.neg s.pos :: le s.pos s.neg :: Γ) ⊢[PRAAx] le s.pos s.neg)
      have ee := natEq eq
      show _ ⊢[PRAAx] s.pos + zero ≐ num 0 + s.neg
      apply deriveNat; ipra_simps; linear_combination -ee

/-- `s² = 0` gives `s = 0`. -/
theorem zt_sq_zero {s : ZT n} (h : Γ ⊢[PRAAx] ZT.eq (s * s) (ZT.natLit 0)) : Γ ⊢[PRAAx] ZT.eq s (ZT.natLit 0) :=
  .orE (zt_dec s) Prf.hyp0 (.botE _ (Prf.impE Prf.hyp0 (zt_no_zero_div Prf.hyp0 h.wk)))

/-- `L(s, t) = R(s, t) = 0` and `r ≠ 0` give `s = t = 0`. -/
theorem no_common_zero (Q : Form n) {p0 p1 p2 s t : ZT n}
    (hr : Γ ⊢[PRAAx] neg (ZT.eq (Q.r p0 p1 p2) (ZT.natLit 0)))
    (hL : Γ ⊢[PRAAx] ZT.eq (Q.L p0 p1 p2 s t) (ZT.natLit 0)) (hR : Γ ⊢[PRAAx] ZT.eq (Q.R s t) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq s (ZT.natLit 0) ⋏ ZT.eq t (ZT.natLit 0) := by
  have eL := ZT.toZ_eq hL; have eR := ZT.toZ_eq hR
  have is := ZT.toZ_eq (Q.identity_s (Γ := Γ) p0 p1 p2 s t)
  have it := ZT.toZ_eq (Q.identity_t (Γ := Γ) p0 p1 p2 s t)
  have zs : Γ ⊢[PRAAx] ZT.eq (Q.r p0 p1 p2 * (s * s)) (ZT.natLit 0) := by
    refine ZT.derive ?_
    simp only [ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_add, ZT.toZ_natLit] at is eL eR ⊢
    try push_cast at eL eR ⊢
    rw [eL, eR] at is; linear_combination is
  have zt : Γ ⊢[PRAAx] ZT.eq (Q.r p0 p1 p2 * (t * t)) (ZT.natLit 0) := by
    refine ZT.derive ?_
    simp only [ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_add, ZT.toZ_natLit] at it eL eR ⊢
    try push_cast at eL eR ⊢
    rw [eL, eR] at it; linear_combination it
  exact .andI (zt_sq_zero (zt_no_zero_div hr zs)) (zt_sq_zero (zt_no_zero_div hr zt))

end LeanProofs.IPRA.DiophantineNumberTheory.ConicNonzero
