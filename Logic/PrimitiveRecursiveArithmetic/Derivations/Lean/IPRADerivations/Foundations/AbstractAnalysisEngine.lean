import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Analysis.RationalClosure
import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.DiophantineNumberTheory.AperyMultibound
import IPRADerivations.DiophantineNumberTheory.SimultaneousGrid
import IPRADerivations.Core.LinearCombination

/-!
# The elementary quantitative engine of abstract analysis

Packet: `foundations/ipra_abstract_analysis_2026-11-20`, `sections/foundations.tex` and `sections/hilbert.tex`
("The elementary quantitative engine"). Rationals are cleared of denominators; a ratio `q = a/b` with
`b = a + d` has gap `δ = d/b`.

* `separation` (`lem:separation`, "Rational separation"): if `2^k r ≤ 2^k s + C` for every `k` (one object
  premise, `r ≤ s + C 2^{−k}`), then `r ≤ s`, by deciding `s < r` and instantiating `k = C` with `C < 2^C`;
* `perturbed` (`lem:perturb`, (H3)): from `b e_{j+1} ≤ a e_j + b η` for all `j` and `e_0 ≤ R`,
  `b^j d e_j ≤ d a^j R + b^{j+1} η`, i.e. `e_j ≤ q^j R + η/δ`, by quantifier-free induction with the premise
  outside the matrix;
* `clock_bernoulli`, `clock_half`, `clock` (`lem:clock`, (H4)): `(b + j d) a^j ≤ b^{j+1}`
  (`(1 + jδ)(1 − δ)^j ≤ 1`); if `h d ≥ b` then `2 a^h ≤ b^h` (`q^h ≤ 1/2`); and for
  `N = h(n + 3 + R)`, `2^{n+3} R a^N ≤ b^N` (`R q^N ≤ 2^{−n−3}`);
* `coercive_gap` (`lem:coercive-contraction`, (H6) for the scalar data): with `Z = ‖z‖²`, `P = ⟨Az, z⟩`,
  `Q = ‖Az‖²`, `mZ ≤ P` and `Q ≤ M²Z` give `m²Q + m²M²Z ≤ 2mM²P`, i.e.
  `M⁴‖z − λAz‖² = M⁴Z − 2mM²P + m²Q ≤ (M⁴ − m²M²)Z` for `λ = m/M²`, `δ = m²/(2M²)`; and
  `gap_square`: `4(M⁴ − m²M²) ≤ (2M² − m²)²`, i.e. `1 − 2δ ≤ (1 − δ)²`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.AbstractAnalysisEngine

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.RationalClosure (succ_le_two_pow)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound (mul_pw)
open LeanProofs.IPRA.DiophantineNumberTheory.SimultaneousGrid (cancel_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Rational separation -/

/-- `lem:separation`: `r ≤ s + C 2^{−k}` for every `k` gives `r ≤ s`. -/
theorem separation {r s C : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (le (pw two (var 0) * Syn.shift r) (pw two (var 0) * Syn.shift s + Syn.shift C))) :
    Γ ⊢[PRAAx] le r s := by
  have hC := Prf.allE C h
  simp only [subst_le, PTm.subst_add, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at hC
  refine .orE (lt_or_le s r) ?_ Prf.hyp0
  have hlt : (lt s r :: Γ) ⊢[PRAAx] le (succ s) r := Prf.hyp0
  have hp := succ_le_two_pow (Γ := lt s r :: Γ) C
  have hcon : (lt s r :: Γ) ⊢[PRAAx] lt (pw two C * s + C) (pw two C * r) := by
    show _ ⊢[PRAAx] le (succ (pw two C * s + C)) (pw two C * r)
    ipra_le 𝔟 (pw two C) * sl hlt + sl hp
  exact le_lt_absurd _ hC.wk hcon

/-! ## Perturbed contraction -/

section Perturb

variable (e : PTm 2) (a d R η x : PTm n)

/-- The invariant `b^j d e_j ≤ d a^j R + b^{j+1} η`, `b = a + d`. -/
abbrev pInv (j : PTm n) : Fm PTm n :=
  le (pw (a + d) j * (d * inst2 e j x)) (d * pw a j * R + pw (a + d) (succ j) * η)

end Perturb

/-- `lem:perturb` (H3): `e_j ≤ q^j R + η/δ`, cleared. -/
theorem perturbed (e : PTm 2) {a d R η x : PTm n} (j : PTm n)
    (h0 : Γ ⊢[PRAAx] le (inst2 e zero x) R)
    (hs : Γ ⊢[PRAAx] Fm.all (le ((Syn.shift a + Syn.shift d) * inst2 e (succ (var 0)) (Syn.shift x))
      (Syn.shift a * inst2 e (var 0) (Syn.shift x) + (Syn.shift a + Syn.shift d) * Syn.shift η))) :
    Γ ⊢[PRAAx] pInv e a d R η x j := by
  have hall : Γ ⊢[PRAAx] Fm.all (pInv e (Syn.shift a) (Syn.shift d) (Syn.shift R) (Syn.shift η)
      (Syn.shift x) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [pInv, subst_le, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_inst2, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      have p0 := natEq (pw_zero (Γ := Γ) (a + d))
      have p1 := natEq (pw_succ (Γ := Γ) (a + d) zero)
      have q0 := natEq (pw_zero (Γ := Γ) a)
      ipra_le 𝔟 d * sl h0 + 𝔟 (a + d) * 𝔟 η using
        rw [p1, p0, q0]; ring
    · simp only [pInv, subst_le, PTm.subst_add, PTm.subst_mul, subst_ap2, subst_inst2, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      let a' := Syn.shift a
      let d' := Syn.shift d
      let R' := Syn.shift R
      let η' := Syn.shift η
      let x' := Syn.shift x
      let Δ := pInv e a' d' R' η' x' (var 0) :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] le (pw (a' + d') (var 0) * (d' * inst2 e (var 0) x'))
          (d' * pw a' (var 0) * R' + pw (a' + d') (succ (var 0)) * η') := Prf.hyp0
      have hk : Δ ⊢[PRAAx] le ((a' + d') * inst2 e (succ (var 0)) x')
          (a' * inst2 e (var 0) x' + (a' + d') * η') := hs.allOpen.wk
      have f1 := natEq (pw_succ (Γ := Δ) (a' + d') (var 0))
      have f2 := natEq (pw_succ (Γ := Δ) (a' + d') (succ (var 0)))
      have f3 := natEq (pw_succ (Γ := Δ) a' (var 0))
      show Δ ⊢[PRAAx] le (pw (a' + d') (succ (var 0)) * (d' * inst2 e (succ (var 0)) x'))
        (d' * pw a' (succ (var 0)) * R' + pw (a' + d') (succ (succ (var 0))) * η')
      ipra_le 𝔟 (pw (a' + d') (var 0)) * 𝔟 d' * sl hk + 𝔟 a' * sl ih with
        (𝔟 d' * 𝔟 R') * f3 + 𝔟 η' * f2 + (𝔟 η' * 𝔟 d' - 𝔟 d' * 𝔟 (inst2 e (succ (var 0)) x')) * f1
  have hj := Prf.allE j hall
  simpa [pInv] using hj

/-! ## A clock without logarithms -/

theorem clock_base (a d : PTm n) :
    Γ ⊢[PRAAx] le ((a + d + zero * d) * pw a zero) (pw (a + d) (succ zero)) := by
  have p0 := natEq (pw_zero (Γ := Γ) a)
  have p1 := natEq (pw_succ (Γ := Γ) (a + d) zero)
  have p2 := natEq (pw_zero (Γ := Γ) (a + d))
  ipra_le 0 using
    rw [p1, p0, p2]; ring

theorem clock_step {j a d : PTm n}
    (ih : Γ ⊢[PRAAx] le ((a + d + j * d) * pw a j) (pw (a + d) (succ j))) :
    Γ ⊢[PRAAx] le ((a + d + succ j * d) * pw a (succ j)) (pw (a + d) (succ (succ j))) := by
  have g1 := natEq (pw_succ (Γ := Γ) a j)
  have g2 := natEq (pw_succ (Γ := Γ) (a + d) (succ j))
  ipra_le (𝔟 a + 𝔟 d) * sl ih + 𝔟 (pw a j) * (𝔟 j + 1) * 𝔟 d ^ 2 with
    g2 - ((𝔟 a + 𝔟 d) + (𝔟 j + 1) * 𝔟 d) * g1

/-- Variables `0 = j` (induction), `1 = a`, `2 = d`. -/
private abbrev cF : Fm PTm 3 :=
  le ((var 1 + var 2 + var 0 * var 2) * pw (var 1) (var 0)) (pw (var 1 + var 2) (succ (var 0)))

private theorem c₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] cF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp
    exact clock_base _ _
  · simp
    exact clock_step Prf.hyp0

/-- `(1 + jδ)(1 − δ)^j ≤ 1`, cleared: `(b + j d) a^j ≤ b^{j+1}` for `b = a + d`. -/
theorem clock_bernoulli (j a d : PTm n) :
    Γ ⊢[PRAAx] le ((a + d + j * d) * pw a j) (pw (a + d) (succ j)) := by
  have h := inst (Γ := Γ) c₀ (![j, a, d] : Fin 3 → PTm n)
  simpa using h

/-- `hδ ≥ 1` gives `q^h ≤ 1/2`: `2 a^h ≤ b^h`. -/
theorem clock_half {a d h : PTm n} (hd : Γ ⊢[PRAAx] le one d) (hh : Γ ⊢[PRAAx] le (a + d) (h * d)) :
    Γ ⊢[PRAAx] le (two * pw a h) (pw (a + d) h) := by
  have C := clock_bernoulli (Γ := Γ) h a d
  have e := natEq (pw_succ (Γ := Γ) (a + d) h)
  refine cancel_pos (X := a + d) (by ipra_le sl hd + 𝔟 a) ?_
  ipra_le sl C + 𝔟 (pw a h) * sl hh with e

/-- (H4): for `N = h(n + 3 + R)`, `R q^N ≤ 2^{−n−3}`, cleared: `2^{n+3} R a^N ≤ b^N`. -/
theorem clock {a d h R : PTm n} (hd : Γ ⊢[PRAAx] le one d) (hh : Γ ⊢[PRAAx] le (a + d) (h * d)) (k : PTm n) :
    Γ ⊢[PRAAx] le (pw two (k + num 3) * R * pw a (h * ((k + num 3) + R)))
      (pw (a + d) (h * ((k + num 3) + R))) := by
  have hh2 := clock_half hd hh
  have P := pw_le_pw ((k + num 3) + R) hh2
  have e1 := natEq (mul_pw (Γ := Γ) two (pw a h) ((k + num 3) + R))
  have e2 := natEq (pw_mul (Γ := Γ) a h ((k + num 3) + R))
  have e3 := natEq (pw_mul (Γ := Γ) (a + d) h ((k + num 3) + R))
  have e4 := natEq (pw_add (Γ := Γ) two (k + num 3) R)
  have hRp := succ_le_two_pow (Γ := Γ) R
  ipra_le sl P + 𝔟 (pw two (k + num 3)) * 𝔟 (pw a (h * ((k + num 3) + R))) * (sl hRp + 1) with
    e1 - e3 + 𝔟 (pw two ((k + num 3) + R)) * e2 + 𝔟 (pw a (h * ((k + num 3) + R))) * e4

/-! ## Coercivity supplies the contraction gap -/

/-- (H6), scalar data: `mZ ≤ P`, `Q ≤ M²Z` give `m²Q + m²M²Z ≤ 2mM²P`, i.e.
`M⁴‖z − λAz‖² ≤ (M⁴ − m²M²)‖z‖²` for `λ = m/M²`. -/
theorem coercive_gap {m M Z P Q : PTm n} (hP : Γ ⊢[PRAAx] le (m * Z) P) (hQ : Γ ⊢[PRAAx] le Q (M * M * Z)) :
    Γ ⊢[PRAAx] le (m * m * Q + m * m * (M * M) * Z) (num 2 * m * (M * M) * P) := by
  ipra_le 2 * 𝔟 m * 𝔟 M ^ 2 * sl hP + 𝔟 m ^ 2 * sl hQ

/-- `(1 − δ)² = (1 − 2δ) + δ²` for `δ = m²/(2M²)`, cleared by `4M⁴`. -/
theorem gap_square (m M : ZT n) :
    Γ ⊢[PRAAx] ZT.eq ((ZT.natLit 2 * (M * M) - m * m) * (ZT.natLit 2 * (M * M) - m * m))
      (ZT.natLit 4 * (M * M * (M * M) - m * m * (M * M)) + m * m * (m * m)) := by
  ipra_lc

end LeanProofs.IPRA.Foundations.AbstractAnalysisEngine
