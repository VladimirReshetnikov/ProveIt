import IPRADerivations.Analysis.RationalArithmetic.Powers.PowerSums
import IPRADerivations.Core.OrderCertificates

/-!
# The finite fundamental theorem of calculus

Packets: `analysis/stirling_ipra` (`stirling_ipra.tex`, `eq:FTCfinite`), `analysis/taylor_cauchy_ipra`
(`report.tex`, Lemma `lem:ftc`, `eq:finiteftc`) and `analysis/calculus_ipra` (Section `sec:FTC`, the
telescoping step of `thm:ftc2`): if `|G(v) − G(u) − (v − u) F(u)| ≤ B (v − u)²` on each cell of a uniform
mesh, then `|h ∑_{j<N} F(u_j) − (G(b) − G(a))| ≤ B (b − a)²/N`. "This is merely the triangle inequality and
telescoping; a fundamental theorem of calculus is not assumed."

For sampled data with natural values, the integrand is given by its positive and negative parts
`F⁺(j, x)`, `F⁻(j, x)` (already multiplied by the cell width), and `E` bounds the error of one cell:

* `ftc_upper`: if `G(j + 1) + F⁻(j) ≤ G(j) + F⁺(j) + E` for `j < N`, then
  `G(N) + ∑_{j<N} F⁻(j) ≤ G(0) + ∑_{j<N} F⁺(j) + N E`;
* `ftc_lower`: if `G(j) + F⁺(j) ≤ G(j + 1) + F⁻(j) + E` for `j < N`, then
  `G(0) + ∑_{j<N} F⁺(j) ≤ G(N) + ∑_{j<N} F⁻(j) + N E`.

Together: `|(G(N) − G(0)) − ∑ (F⁺ − F⁻)| ≤ N E`. The partial-sum inductions of `WallisRecurrence`,
`WallisFinite` and `EvenPowerIntegrals` are instances of this pattern.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.FiniteFTC

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The partial sums of the upper estimate. -/
abbrev UpInv (G Fpos Fneg : PTm 2) (k x E : PTm n) : Fm PTm n :=
  le (inst2 G k x + ap2 (sumF Fneg) k x) (inst2 G zero x + ap2 (sumF Fpos) k x + k * E)

/-- The partial sums of the lower estimate. -/
abbrev DnInv (G Fpos Fneg : PTm 2) (k x E : PTm n) : Fm PTm n :=
  le (inst2 G zero x + ap2 (sumF Fpos) k x) (inst2 G k x + ap2 (sumF Fneg) k x + k * E)

theorem up_base (G Fpos Fneg : PTm 2) (x E : PTm n) : Γ ⊢[PRAAx] UpInv G Fpos Fneg zero x E := by
  have z1 := natEq (sum_zero (Γ := Γ) Fneg x); have z2 := natEq (sum_zero (Γ := Γ) Fpos x)
  ipra_le 0 using rw [z1, z2]; ring

theorem dn_base (G Fpos Fneg : PTm 2) (x E : PTm n) : Γ ⊢[PRAAx] DnInv G Fpos Fneg zero x E := by
  have z1 := natEq (sum_zero (Γ := Γ) Fneg x); have z2 := natEq (sum_zero (Γ := Γ) Fpos x)
  ipra_le 0 using rw [z1, z2]; ring

theorem up_step {G Fpos Fneg : PTm 2} {k x E : PTm n}
    (c : Γ ⊢[PRAAx] le (inst2 G (succ k) x + inst2 Fneg k x) (inst2 G k x + inst2 Fpos k x + E))
    (ih : Γ ⊢[PRAAx] UpInv G Fpos Fneg k x E) : Γ ⊢[PRAAx] UpInv G Fpos Fneg (succ k) x E := by
  have e1 := natEq (sum_succ' (Γ := Γ) Fneg k x); have e2 := natEq (sum_succ' (Γ := Γ) Fpos k x)
  ipra_le sl ih + sl c using rw [e1, e2]; ring

theorem dn_step {G Fpos Fneg : PTm 2} {k x E : PTm n}
    (c : Γ ⊢[PRAAx] le (inst2 G k x + inst2 Fpos k x) (inst2 G (succ k) x + inst2 Fneg k x + E))
    (ih : Γ ⊢[PRAAx] DnInv G Fpos Fneg k x E) : Γ ⊢[PRAAx] DnInv G Fpos Fneg (succ k) x E := by
  have e1 := natEq (sum_succ' (Γ := Γ) Fneg k x); have e2 := natEq (sum_succ' (Γ := Γ) Fpos k x)
  ipra_le sl ih + sl c using rw [e1, e2]; ring

/-- `eq:FTCfinite`, upper half: if `G(j+1) + F⁻(j) ≤ G(j) + F⁺(j) + E` for `j < N`, then
`G(N) + ∑_{j<N} F⁻(j) ≤ G(0) + ∑_{j<N} F⁺(j) + N E`. -/
theorem ftc_upper (G Fpos Fneg : PTm 2) (x N E : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 G (succ (var 0)) (Syn.shift x) + inst2 Fneg (var 0) (Syn.shift x))
        (inst2 G (var 0) (Syn.shift x) + inst2 Fpos (var 0) (Syn.shift x) + Syn.shift E))) :
    Γ ⊢[PRAAx] UpInv G Fpos Fneg N x E := by
  let P := UpInv G Fpos Fneg (var 0) (Syn.shift x) (Syn.shift E)
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst N) := by
    refine qfIndUpTo N (le_QF _ _) ?_ ?_
    · simpa [P, UpInv] using up_base (Γ := Γ) G Fpos Fneg x E
    · ipra_ind_simp [P, UpInv, subst_le, subst_ap2, subst_inst2, subst_repl_shift]
      exact .impI (up_step (.impE h.allOpen.wk.wk Prf.hyp0) Prf.hyp1)
  simpa [P, UpInv] using atBound

/-- `eq:FTCfinite`, lower half: if `G(j) + F⁺(j) ≤ G(j+1) + F⁻(j) + E` for `j < N`, then
`G(0) + ∑_{j<N} F⁺(j) ≤ G(N) + ∑_{j<N} F⁻(j) + N E`. -/
theorem ftc_lower (G Fpos Fneg : PTm 2) (x N E : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 G (var 0) (Syn.shift x) + inst2 Fpos (var 0) (Syn.shift x))
        (inst2 G (succ (var 0)) (Syn.shift x) + inst2 Fneg (var 0) (Syn.shift x) + Syn.shift E))) :
    Γ ⊢[PRAAx] DnInv G Fpos Fneg N x E := by
  let P := DnInv G Fpos Fneg (var 0) (Syn.shift x) (Syn.shift E)
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst N) := by
    refine qfIndUpTo N (le_QF _ _) ?_ ?_
    · simpa [P, DnInv] using dn_base (Γ := Γ) G Fpos Fneg x E
    · ipra_ind_simp [P, DnInv, subst_le, subst_ap2, subst_inst2, subst_repl_shift]
      exact .impI (dn_step (.impE h.allOpen.wk.wk Prf.hyp0) Prf.hyp1)
  simpa [P, DnInv] using atBound

end LeanProofs.IPRA.Analysis.FiniteFTC
