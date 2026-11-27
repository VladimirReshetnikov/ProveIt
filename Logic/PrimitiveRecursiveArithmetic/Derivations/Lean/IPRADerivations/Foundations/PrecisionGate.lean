import IPRADerivations.Core.OrderCertificates
import IPRADerivations.DiophantineNumberTheory.FLTMultiples
import IPRADerivations.Core.BoundedSums

/-!
# A precision budget for a finite arithmetic table

Packet: `foundations/ipra_framework`, `paper/sections/04_analytic_tools.tex`, Lemma `core:gate`
("A precision budget for a finite arithmetic table"): in a table of `N` gates with magnitude bound `B` and
`L = 2B + 3`, if corresponding inputs differ by at most `δ` and each gate adds a rounding error at most
`δ`, the error after the first `j` gates is at most `L^j δ`.

Rationals are numerators over a common denominator.

* `gate_mul`: the multiplication gate. From `a ≤ a′ + e`, `b ≤ b′ + e` and the magnitudes `a ≤ B`,
  `b′ ≤ B + 1`, `a b ≤ a′ b′ + (2B + 1) e`; this is `|ab − a′b′| ≤ |a| |b − b′| + |b′| |a − a′|`. (The
  addition gate is `sum_modulus` of `Foundations/PrecisionArithmetic`, with the factor `2 ≤ 2B + 1`.)
* `gate_step`: one gate. If the new error is at most `K e + δ` and `e ≤ (K + 2)^j δ`, it is at most
  `(K + 2)^{j+1} δ`; with `K = 2B + 1` the base is `L = 2B + 3`.
* `gate_all`: for an error sequence `E(j, x)` with `E(0) ≤ δ` and `E(j + 1) ≤ K E(j) + δ` for `j < N`,
  `E(j) ≤ (K + 2)^j δ` for every `j ≤ N`.

The side condition "errors at most one", which keeps the second operands within `B + 1`, and the final
comparison of `L^{N+1} δ` with `2^{-s}` are hypotheses of the application.
-/

namespace LeanProofs.IPRA.Foundations.PrecisionGate

open_ipra exports

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The multiplication gate: `a b ≤ a′ b′ + (2B + 1) e`. -/
theorem gate_mul {a a' b b' B e : PTm n} (ha : Γ ⊢[PRAAx] le a (a' + e)) (hb : Γ ⊢[PRAAx] le b (b' + e))
    (haB : Γ ⊢[PRAAx] le a B) (hbB : Γ ⊢[PRAAx] le b' (succ B)) :
    Γ ⊢[PRAAx] le (a * b) (a' * b' + succ (two * B) * e) := by
  ipra_le 𝔟 a * sl hb + 𝔟 b' * sl ha + 𝔟 e * sl haB + 𝔟 e * sl hbB

/-- One gate: an error `e ≤ (K + 2)^j δ` becomes at most `(K + 2)^{j+1} δ`. -/
theorem gate_step {K δ e e' j : PTm n} (hr : Γ ⊢[PRAAx] le e' (K * e + δ))
    (ih : Γ ⊢[PRAAx] le e (pw (succ (succ K)) j * δ)) :
    Γ ⊢[PRAAx] le e' (pw (succ (succ K)) (succ j) * δ) := by
  have ep := natEq (pw_succ (Γ := Γ) (succ (succ K)) j)
  have epos := natEq (pw_pos (Γ := Γ) (succ K) j)
  ipra_le sl hr + 𝔟 K * sl ih + (2 * 𝔟 (pred (pw (succ (succ K)) j)) + 1) * 𝔟 δ using
    rw [ep]
    linear_combination 2 * 𝔟 δ * epos

theorem gate_guard {K δ e e' j N : PTm n} (hjN : Γ ⊢[PRAAx] le (succ j) N)
    (hr : Γ ⊢[PRAAx] le e' (K * e + δ))
    (ih : Γ ⊢[PRAAx] le j N ⟶ le e (pw (succ (succ K)) j * δ)) :
    Γ ⊢[PRAAx] le e' (pw (succ (succ K)) (succ j) * δ) :=
  gate_step hr (Prf.impE ih (le_trans (le_succ_self j) hjN))

/-- `core:gate`: the error after `j ≤ N` gates is at most `(K + 2)^j δ`. -/
theorem gate_all {E : PTm 2} {N x K δ : PTm n} (h0 : Γ ⊢[PRAAx] le (inst2 E zero x) δ)
    (hrec : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 E (succ (var 0)) (Syn.shift x)) (Syn.shift K * inst2 E (var 0) (Syn.shift x) + Syn.shift δ))) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      le (inst2 E (var 0) (Syn.shift x)) (pw (succ (succ (Syn.shift K))) (var 0) * Syn.shift δ)) := by
  refine qfIndAllUpTo N (le_QF _ _) ?_ ?_
  · ipra_ind_simp [subst_le, subst_ap2, subst_inst2, Syn.subst_inst_shift]
    have p0 := natEq (pw_zero (Γ := Γ) (succ (succ K)))
    ipra_le sl h0 using rw [p0]; ring
  · ipra_ind_simp [subst_le, subst_ap2, subst_inst2, subst_repl_shift]
    exact .impI (gate_step (.impE hrec.allOpen.wk.wk Prf.hyp0) Prf.hyp1)

/-- The error at a stage `j ≤ N`. -/
theorem gate_at {E : PTm 2} {N x K δ j : PTm n} (h0 : Γ ⊢[PRAAx] le (inst2 E zero x) δ)
    (hrec : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 E (succ (var 0)) (Syn.shift x)) (Syn.shift K * inst2 E (var 0) (Syn.shift x) + Syn.shift δ)))
    (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx] le (inst2 E j x) (pw (succ (succ K)) j * δ) := by
  have a := Prf.allE j (gate_all h0 hrec)
  simp only [Fm.subst_imp, subst_le, subst_ap2, subst_inst2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ] at a
  exact Prf.impE a hj

end LeanProofs.IPRA.Foundations.PrecisionGate
