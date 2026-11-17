import IPRADerivations.Core.Tactic

/-!
# Instantiation into a context and staged proof graphs

Packet: `ipra_staged_contract_kernel_2026-11-15`, `lem:instantiate-into` and `thm:staged-graph`.

* `instantiate_into` (`lem:instantiate-into`): a local derivation `Δ ⊢ A`, a substitution `σ` of global
  terms and an inclusion `Δ[σ] ⊆ Θ` give `Θ ⊢ A[σ]` (`Prf.subst` followed by `Prf.weaken`);
* `cut_all`: if every formula of `Θ` is derivable from `Γ` and `Θ ⊢ A`, then `Γ ⊢ A`;
* `staged_graph` (`thm:staged-graph`): for a static proof graph over `Γ` (nodes `v` with local
  derivations `d_v : Δ_v ⊢ A_v` and substitutions `σ_v`, such that every formula of `Δ_v[σ_v]` lies in
  `Γ` or equals `A_u[σ_u]` for an earlier node `u < v`), every node goal `Γ ⊢ A_v[σ_v]` is derivable.
  As in the packet, the induction on the node sequence is in the Lean metatheory: it constructs a
  finite object derivation and adds no induction axiom.
-/

namespace LeanProofs.IPRA.Foundations.StagedGraph

open LeanProofs.ConciseIPRA LeanProofs.IPRA

variable {n : ℕ}

/-- `lem:instantiate-into`. -/
theorem instantiate_into {k : ℕ} {Δ : List (Fm PTm k)} {A : Fm PTm k} (d : Δ ⊢[PRAAx] A) (σ : Fin k → PTm n)
    {Θ : List (Fm PTm n)} (s : Δ.map (fun ψ => ψ.subst σ) ⊆ Θ) : Θ ⊢[PRAAx] A.subst σ :=
  (d.subst σ).weaken s

/-- Discharging a list of derivable hypotheses. -/
theorem cut_all {Γ : List (Fm PTm n)} (Θ : List (Fm PTm n)) (hs : ∀ φ ∈ Θ, Γ ⊢[PRAAx] φ) {A : Fm PTm n}
    (h : Θ ⊢[PRAAx] A) : Γ ⊢[PRAAx] A := by
  induction Θ generalizing A with
  | nil => exact h.weaken (List.nil_subset _)
  | cons ψ Θ ih =>
    exact .impE (ih (fun φ hφ => hs φ (List.mem_cons_of_mem _ hφ)) (.impI h)) (hs ψ List.mem_cons_self)

/-- A node of a static proof graph: a local derivation and its instantiation. -/
structure Node (n : ℕ) where
  k : ℕ
  Δ : List (Fm PTm k)
  A : Fm PTm k
  σ : Fin k → PTm n
  d : Δ ⊢[PRAAx] A

/-- The public goal of a node. -/
def Node.goal (v : Node n) : Fm PTm n := v.A.subst v.σ

/-- `thm:staged-graph`: every node goal of a static proof graph is derivable from `Γ`. -/
theorem staged_graph {Γ : List (Fm PTm n)} (node : ℕ → Node n)
    (avail : ∀ v, ∀ φ ∈ (node v).Δ.map (fun ψ => ψ.subst (node v).σ), φ ∈ Γ ∨ ∃ u < v, φ = (node u).goal) :
    ∀ v, Γ ⊢[PRAAx] (node v).goal := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    refine cut_all ((node v).Δ.map (fun ψ => ψ.subst (node v).σ)) (fun φ hφ => ?_) ((node v).d.subst _)
    rcases avail v φ hφ with h | ⟨u, hu, rfl⟩
    · exact .hyp h
    · exact ih u hu

end LeanProofs.IPRA.Foundations.StagedGraph
