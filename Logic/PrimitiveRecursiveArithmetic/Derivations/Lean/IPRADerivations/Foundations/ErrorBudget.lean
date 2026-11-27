import IPRADerivations.Core.OrderCertificates
import Mathlib.Algebra.BigOperators.Fin
import IPRADerivations.Core.Header

/-!
# Weighted error budgets on finite dependency graphs

Packet: `foundations/ipra_observable_analysis_2026-11-20`, `lean/ObservableAnalysis/Budget.lean` (host-level Lean
there): `weighted_budget` and `weighted_budget_supersolution`. "A nonnegative weight vector satisfying the displayed
finite balance converts local errors into the final bound … A verified nonnegative *supersolution* is
sufficient. This variant may certify a cyclic error system."

For `k` nodes (any fixed `k`), natural terms `e_v` (errors), `δ_v` (local errors), `b_u` (final selection),
`W_v` (weights) and `L_{vu}` (error propagation), with the local estimates and the supersolution balance as
derived hypotheses:

* `budget`: `e_v ≤ δ_v + ∑_u L_{vu} e_u` for all `v` and `b_u + ∑_v W_v L_{vu} ≤ W_u` for all `u` give
  `∑_u b_u e_u ≤ ∑_v W_v δ_v`.

The certificate is explicit: `∑_v W_v δ_v − ∑_u b_u e_u = ∑_v W_v s_v + ∑_u e_u t_u`, with `s_v, t_u` the
slacks of the two hypotheses, by one exchange of a double sum. The graph may be cyclic.
-/

namespace LeanProofs.IPRA.Foundations.ErrorBudget

open_ipra exports

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `∑_{i<k} f_i`. -/
def nsum : {k : ℕ} → (Fin k → PTm n) → PTm n
  | 0, _ => zero
  | _ + 1, f => f 0 + nsum fun i => f i.succ

theorem toG_nsum : {k : ℕ} → (f : Fin k → PTm n) →
    Groth.ι (Q.mk Γ (nsum f)) = ∑ i, Groth.ι (Q.mk Γ (f i))
  | 0, f => by simp [nsum]
  | k + 1, f => by
    rw [Fin.sum_univ_succ, ← toG_nsum (fun i => f i.succ)]
    simp only [nsum, Q.mk_add, map_add]

/-- The budget identity in any commutative ring. -/
theorem budget_identity {R : Type*} [CommRing R] {k : ℕ} (E D B Wt S T : Fin k → R) (Lm : Fin k → Fin k → R)
    (hS : ∀ v, D v + ∑ u, Lm v u * E u = E v + S v)
    (hT : ∀ u, Wt u = B u + ∑ v, Wt v * Lm v u + T u) :
    ∑ v, Wt v * D v = ∑ u, B u * E u + (∑ v, Wt v * S v + ∑ u, E u * T u) := by
  have hS' : ∀ v, S v = D v + ∑ u, Lm v u * E u - E v := fun v => by linear_combination -(hS v)
  have hT' : ∀ u, T u = Wt u - B u - ∑ v, Wt v * Lm v u := fun u => by linear_combination -(hT u)
  have h1 : ∑ v, Wt v * S v = ∑ v, Wt v * D v + ∑ v, ∑ u, Wt v * (Lm v u * E u) - ∑ v, Wt v * E v := by
    simp only [hS', _root_.mul_sub, _root_.mul_add, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h2 : ∑ u, E u * T u = ∑ u, E u * Wt u - ∑ u, E u * B u - ∑ u, ∑ v, E u * (Wt v * Lm v u) := by
    simp only [hT', _root_.mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  have h3 : ∑ v, ∑ u, Wt v * (Lm v u * E u) = ∑ u, ∑ v, E u * (Wt v * Lm v u) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  have h4 : ∑ v, Wt v * E v = ∑ u, E u * Wt u := Finset.sum_congr rfl fun u _ => by ring
  have h5 : ∑ u, B u * E u = ∑ u, E u * B u := Finset.sum_congr rfl fun u _ => by ring
  rw [h1, h2, h3, h4, h5]
  ring

/-- The weighted error budget. -/
theorem budget {k : ℕ} (e δ b W : Fin k → PTm n) (L : Fin k → Fin k → PTm n)
    (hlocal : ∀ v, Γ ⊢[PRAAx] le (e v) (δ v + nsum fun u => L v u * e u))
    (hbal : ∀ u, Γ ⊢[PRAAx] le (b u + nsum fun v => W v * L v u) (W u)) :
    Γ ⊢[PRAAx] le (nsum fun u => b u * e u) (nsum fun v => W v * δ v) := by
  refine le_of_eq_add (d := (nsum fun v => W v * monus (δ v + nsum fun u => L v u * e u) (e v)) +
    nsum fun u => e u * monus (W u) (b u + nsum fun v => W v * L v u)) ?_
  apply deriveNat
  have hs : ∀ v, Groth.ι (Q.mk Γ (δ v)) + ∑ u, Groth.ι (Q.mk Γ (L v u)) * Groth.ι (Q.mk Γ (e u)) =
      Groth.ι (Q.mk Γ (e v)) + Groth.ι (Q.mk Γ (monus (δ v + nsum fun u => L v u * e u) (e v))) := by
    intro v
    have h := natEq (eq_add_of_le (hlocal v))
    simp only [Q.mk_add, Q.mk_mul, map_add, map_mul, toG_nsum] at h
    exact h
  have ht : ∀ u, Groth.ι (Q.mk Γ (W u)) = Groth.ι (Q.mk Γ (b u)) +
      ∑ v, Groth.ι (Q.mk Γ (W v)) * Groth.ι (Q.mk Γ (L v u)) +
      Groth.ι (Q.mk Γ (monus (W u) (b u + nsum fun v => W v * L v u))) := by
    intro u
    have h := natEq (eq_add_of_le (hbal u))
    simp only [Q.mk_add, Q.mk_mul, map_add, map_mul, toG_nsum] at h
    exact h
  simp only [Q.mk_add, Q.mk_mul, map_add, map_mul, toG_nsum]
  exact budget_identity (fun u => Groth.ι (Q.mk Γ (e u))) (fun v => Groth.ι (Q.mk Γ (δ v)))
    (fun u => Groth.ι (Q.mk Γ (b u))) (fun v => Groth.ι (Q.mk Γ (W v)))
    (fun v => Groth.ι (Q.mk Γ (monus (δ v + nsum fun u => L v u * e u) (e v))))
    (fun u => Groth.ι (Q.mk Γ (monus (W u) (b u + nsum fun v => W v * L v u))))
    (fun v u => Groth.ι (Q.mk Γ (L v u))) hs ht

end LeanProofs.IPRA.Foundations.ErrorBudget

export_ipra Foundations.ErrorBudget (nsum toG_nsum)
