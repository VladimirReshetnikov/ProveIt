import IPRADerivations.Core.SumLemmas
import IPRADerivations.Core.OrderCertificates

/-!
# The Bernstein coefficient certificate

Packet: `analysis/calculus_ipra`, Section `sec:remainder` (`eq:Bernsteinrec`, `eq:Bernsteinweights`,
`eq:halfbound`): the bound `|P_n(t)| ≤ 2^{-n}` on `[0, 1]` is proved there by a finite certificate on
Bernstein coefficients. Its two arithmetic steps are derived here, with absolute values supplied as natural
numbers.

* `weighted_bound`: `h_i ≤ K w_i` for `i < N` gives `∑ h ≤ K ∑ w`;
* `convex_bound`: with weights of total `W` (for the Bernstein basis values, partition of unity), the same
  hypothesis gives `∑ h ≤ K W`: a coefficient bound `|b_i| ≤ K` bounds the value of the polynomial;
* `ramp_bound`: `h_i ≤ K (i + 1)` for `i < N` gives `2 ∑_{i<N} h_i ≤ K N (N + 1)`;
* `bernstein_contraction`: for the two blocks of the numerator of `eq:Bernsteinrec`, the lower block
  `h_i = (i + 1)|b_i|`, `i < j`, and the reflected upper block `g_i = (i + 1)|b_{n-1-i}|`, `i < m`, with
  `j + m = n` and all `|b_i| ≤ K`: `2 (∑ h + ∑ g) ≤ K n (n + 1)`. After division by `n (n + 1)` the
  maximal absolute Bernstein coefficient contracts by `1/2`, which is the inductive step of `eq:halfbound`.

The weight identity `eq:Bernsteinweights` itself is `bernstein_weights` of
`Analysis/FiniteDifferenceIdentities`; the monomial remainder `eq:monomialremainder` is `power_inc_lower`
and `power_inc_upper` of `Analysis/PowerIncrement`. The coefficient recursion of the polynomials `P_n` and
the Bernstein form of the antiderivative are not formalized here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.BernsteinContraction

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Weighted sums -/

theorem weighted_step {h w : PTm 2} {k x K : PTm n}
    (hk : Γ ⊢[PRAAx] le (inst2 h k x) (K * inst2 w k x))
    (ih : Γ ⊢[PRAAx] le (ap2 (sumF h) k x) (K * ap2 (sumF w) k x)) :
    Γ ⊢[PRAAx] le (ap2 (sumF h) (succ k) x) (K * ap2 (sumF w) (succ k) x) := by
  have e₁ := natEq (sum_succ' (Γ := Γ) h k x)
  have e₂ := natEq (sum_succ' (Γ := Γ) w k x)
  ipra_le sl ih + sl hk using rw [e₁, e₂]; ring

theorem weighted_guard {h w : PTm 2} {k x K N : PTm n} (hkN : Γ ⊢[PRAAx] le (succ k) N)
    (hk : Γ ⊢[PRAAx] le (inst2 h k x) (K * inst2 w k x))
    (ih : Γ ⊢[PRAAx] le k N ⟶ le (ap2 (sumF h) k x) (K * ap2 (sumF w) k x)) :
    Γ ⊢[PRAAx] le (ap2 (sumF h) (succ k) x) (K * ap2 (sumF w) (succ k) x) :=
  weighted_step hk (Prf.impE ih (le_trans (le_succ_self k) hkN))

/-- `h_i ≤ K w_i` for `i < N` gives `∑ h ≤ K ∑ w`. -/
theorem weighted_bound {h w : PTm 2} {N x K : PTm n}
    (hp : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 h (var 0) (Syn.shift x)) (Syn.shift K * inst2 w (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (ap2 (sumF h) N x) (K * ap2 (sumF w) N x) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      le (ap2 (sumF h) (var 0) (Syn.shift x)) (Syn.shift K * ap2 (sumF w) (var 0) (Syn.shift x))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      have z₁ := natEq (sum_zero (Γ := le zero N :: Γ) h x)
      have z₂ := natEq (sum_zero (Γ := le zero N :: Γ) w x)
      ipra_le 0 using rw [z₁, z₂]; ring
    · simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact .impI (weighted_guard Prf.hyp0 (Prf.impE hp.allOpen.wk.wk Prf.hyp0) Prf.hyp1)
  have a := Prf.allE N hall
  simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at a
  exact .impE a (le_refl N)

/-- The evaluation bound: with weights of total `W` (partition of unity), `h_i ≤ K w_i` gives
`∑ h ≤ K W`. -/
theorem convex_bound {h w : PTm 2} {N x K W : PTm n}
    (hp : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 h (var 0) (Syn.shift x)) (Syn.shift K * inst2 w (var 0) (Syn.shift x))))
    (hW : Γ ⊢[PRAAx] ap2 (sumF w) N x ≐ W) :
    Γ ⊢[PRAAx] le (ap2 (sumF h) N x) (K * W) := by
  have h₁ := weighted_bound hp
  have e := natEq hW
  ipra_le sl h₁ using rw [e]

/-! ## Ramp weights and the Bernstein contraction -/

theorem ramp_step {h : PTm 2} {k x K : PTm n} (hk : Γ ⊢[PRAAx] le (inst2 h k x) (K * succ k))
    (ih : Γ ⊢[PRAAx] le (two * ap2 (sumF h) k x) (K * (k * succ k))) :
    Γ ⊢[PRAAx] le (two * ap2 (sumF h) (succ k) x) (K * (succ k * succ (succ k))) := by
  have e₁ := natEq (sum_succ' (Γ := Γ) h k x)
  ipra_le sl ih + 2 * sl hk using rw [e₁]; ring

theorem ramp_guard {h : PTm 2} {k x K N : PTm n} (hkN : Γ ⊢[PRAAx] le (succ k) N)
    (hk : Γ ⊢[PRAAx] le (inst2 h k x) (K * succ k))
    (ih : Γ ⊢[PRAAx] le k N ⟶ le (two * ap2 (sumF h) k x) (K * (k * succ k))) :
    Γ ⊢[PRAAx] le (two * ap2 (sumF h) (succ k) x) (K * (succ k * succ (succ k))) :=
  ramp_step hk (Prf.impE ih (le_trans (le_succ_self k) hkN))

/-- `h_i ≤ K (i + 1)` for `i < N` gives `2 ∑_{i<N} h_i ≤ K N (N + 1)`. -/
theorem ramp_bound {h : PTm 2} {N x K : PTm n}
    (hp : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 h (var 0) (Syn.shift x)) (Syn.shift K * succ (var 0)))) :
    Γ ⊢[PRAAx] le (two * ap2 (sumF h) N x) (K * (N * succ N)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      le (two * ap2 (sumF h) (var 0) (Syn.shift x)) (Syn.shift K * (var 0 * succ (var 0)))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      have z₁ := natEq (sum_zero (Γ := le zero N :: Γ) h x)
      ipra_le 0 using rw [z₁]; ring
    · simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact .impI (ramp_guard Prf.hyp0 (Prf.impE hp.allOpen.wk.wk Prf.hyp0) Prf.hyp1)
  have a := Prf.allE N hall
  simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at a
  exact .impE a (le_refl N)

/-- The contraction of `eq:Bernsteinrec`: for the lower block `h_i ≤ K (i + 1)`, `i < j`, and the reflected
upper block `g_i ≤ K (i + 1)`, `i < m`, the numerator satisfies `2 (∑ h + ∑ g) ≤ K (j + m)(j + m + 1)`. -/
theorem bernstein_contraction {h g : PTm 2} {j m x y K : PTm n}
    (hh : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift j) ⟶
      le (inst2 h (var 0) (Syn.shift x)) (Syn.shift K * succ (var 0))))
    (hg : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift m) ⟶
      le (inst2 g (var 0) (Syn.shift y)) (Syn.shift K * succ (var 0)))) :
    Γ ⊢[PRAAx] le (two * (ap2 (sumF h) j x + ap2 (sumF g) m y)) (K * ((j + m) * succ (j + m))) := by
  have r₁ := ramp_bound hh
  have r₂ := ramp_bound hg
  ipra_le sl r₁ + sl r₂ + 2 * 𝔟 K * 𝔟 j * 𝔟 m

end LeanProofs.IPRA.Analysis.BernsteinContraction
