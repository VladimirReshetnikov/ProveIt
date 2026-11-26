import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Analysis.RationalArithmetic.PowerSums

/-!
# The power-gap bound

Packet: `analysis/bohr_mollerup_ipra_2026-11-15`, `paper/bohr_mollerup_ipra.tex`, the lemma "power-gap bound"
(`eq:power-gap`): `0 ≤ B_n(q)^b − A_n(q)^b ≤ b/(n q^{b−1})`. The proof factors
`B^b − A^b = (B − A) ∑_{i<b} B^{b−1−i} A^i` and bounds each of the `b` summands by `U^{b−1}` for an upper
bound `U` of both brackets (`U = 1/q` in the paper), so that `B^b − A^b ≤ (B − A) · b · U^{b−1}`; with
`B − A ≤ 1/n` (`eq:width`) this is `eq:power-gap`.

* `power_gap`: for natural numerators with `B = A + d` and `B ≤ U`, and every `b`,
  `B^{b+1} ≤ A^{b+1} + d (b + 1) U^b`;
* `power_gap_lower`: `A^b ≤ B^b` for `B = A + d` (the left inequality);
* `strict_power_gap` (`foundations/ipra_framework`, `dio:gap`, for naturals `u < v`):
  `u^{e+1} + v^e ≤ v^{e+1}`. With `U = B`, `power_gap` is also the finite loss estimate `dio:loss` of that
  packet, `(X − L)^n ≥ X^n − n L X^{n−1}`.

The induction on `b` avoids the explicit sum: its step is the certificate
`B · (ih) + d (U^{b+1} − A^{b+1}) + d (b + 1) U^b (U − B)`. The bracket width `eq:width` and the bound `1/q`
on the brackets are not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.PowerGap

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

section Gap

variable {A B U d : PTm n}

theorem gap_base (hd : Γ ⊢[PRAAx] B ≐ A + d) :
    Γ ⊢[PRAAx] le (pw B (succ zero)) (pw A (succ zero) + d * (succ zero * pw U zero)) := by
  have e := natEq hd
  have p₁ := natEq (pw_succ (Γ := Γ) B zero); have p₂ := natEq (pw_succ (Γ := Γ) A zero)
  have z₁ := natEq (pw_zero (Γ := Γ) B); have z₂ := natEq (pw_zero (Γ := Γ) A)
  have z₃ := natEq (pw_zero (Γ := Γ) U)
  ipra_le 0 using
    rw [p₁, p₂, z₁, z₂, z₃]
    first | linear_combination e | linear_combination -e

theorem gap_step {b : PTm n} (hd : Γ ⊢[PRAAx] B ≐ A + d) (hU : Γ ⊢[PRAAx] le B U)
    (ih : Γ ⊢[PRAAx] le (pw B (succ b)) (pw A (succ b) + d * (succ b * pw U b))) :
    Γ ⊢[PRAAx] le (pw B (succ (succ b))) (pw A (succ (succ b)) + d * (succ (succ b) * pw U (succ b))) := by
  have e := natEq hd
  have hAU : Γ ⊢[PRAAx] le A U := by ipra_le sl hU + 𝔟 d with e
  have hp := pw_le_pw (succ b) hAU
  have a₁ := natEq (pw_succ (Γ := Γ) B (succ b)); have a₂ := natEq (pw_succ (Γ := Γ) A (succ b))
  have a₃ := natEq (pw_succ (Γ := Γ) U b)
  ipra_le 𝔟 B * sl ih + 𝔟 d * sl hp + 𝔟 d * (𝔟 b + 1) * 𝔟 (pw U b) * sl hU using
    rw [a₁, a₂, a₃]
    linear_combination (-𝔟 (pw A (succ b))) * e

theorem shift_le' {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) :
    Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a) (Syn.shift b) := by
  have e := h.shift
  simp only [Fm.shift, subst_le] at e
  exact e

theorem shift_eq' (hd : Γ ⊢[PRAAx] B ≐ A + d) :
    Γ.map Fm.shift ⊢[PRAAx] Syn.shift B ≐ Syn.shift A + Syn.shift d := by
  have h := hd.shift
  have e : Fm.shift (B ≐ A + d) = (Syn.shift B ≐ Syn.shift A + Syn.shift d) := by
    simp [Fm.shift, Syn.shift]
  rw [e] at h
  exact h

theorem gap_all (hd : Γ ⊢[PRAAx] B ≐ A + d) (hU : Γ ⊢[PRAAx] le B U) :
    Γ ⊢[PRAAx] Fm.all (le (pw (Syn.shift B) (succ (var 0)))
      (pw (Syn.shift A) (succ (var 0)) + Syn.shift d * (succ (var 0) * pw (Syn.shift U) (var 0)))) := by
  ipra_qfind (le_QF _ _) [subst_le, subst_ap2]
  · exact gap_base hd
  · exact gap_step (shift_eq' hd).wk (shift_le' hU).wk Prf.hyp0

/-- `eq:power-gap`, algebraic core: `B^{b+1} ≤ A^{b+1} + (B − A)(b + 1) U^b` for `A ≤ B ≤ U`. -/
theorem power_gap (hd : Γ ⊢[PRAAx] B ≐ A + d) (hU : Γ ⊢[PRAAx] le B U) (b : PTm n) :
    Γ ⊢[PRAAx] le (pw B (succ b)) (pw A (succ b) + d * (succ b * pw U b)) := by
  have a := Prf.allE b (gap_all hd hU)
  simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at a
  exact a

/-- The left inequality of `eq:power-gap`: `A^b ≤ B^b` for `A ≤ B`. -/
theorem power_gap_lower (hd : Γ ⊢[PRAAx] B ≐ A + d) (b : PTm n) : Γ ⊢[PRAAx] le (pw A b) (pw B b) :=
  pw_le_pw b (le_of_eq_add hd)

end Gap

/-- The integer power gap (`foundations/ipra_framework`, `dio:gap`, the case of naturals `u < v`):
`u^{e+1} + v^e ≤ v^{e+1}`, i.e. `v^m − u^m ≥ v^{m−1}`. -/
theorem strict_power_gap {u v : PTm n} (h : Γ ⊢[PRAAx] lt u v) (e : PTm n) :
    Γ ⊢[PRAAx] le (pw u (succ e) + pw v e) (pw v (succ e)) := by
  have h' : Γ ⊢[PRAAx] le (succ u) v := h
  have hu : Γ ⊢[PRAAx] le u v := by ipra_le sl h' + 1
  have hp := pw_le_pw e hu
  have a₁ := natEq (pw_succ (Γ := Γ) u e); have a₂ := natEq (pw_succ (Γ := Γ) v e)
  ipra_le 𝔟 (pw v e) * sl h' + 𝔟 u * sl hp using rw [a₁, a₂]; ring

end LeanProofs.IPRA.Analysis.PowerGap
