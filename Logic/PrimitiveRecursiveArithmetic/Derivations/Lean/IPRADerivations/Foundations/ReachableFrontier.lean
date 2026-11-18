import IPRADerivations.Foundations.OpenContracts

/-!
# Reachability in a proof graph and the residual frontier

Packet: `foundations/ipra_kifcs_framework_2026-11-16`: Lemma "Reachability soundness", Lemma `lem:reach-min`
("Reachability minimality"), Proposition "Union law", Theorem `thm:least-frontier` ("Least residual
frontier"), and the sufficiency of the frontier that these support.

A proof graph is a metalevel object: nodes of a type `α`, the list `parents v` of proof parents of a node,
its exported formula `φ v`, the list `resid v` of residual (boundary) formulas its local rule uses, and its
local rule as an open contract from the parents' formulas and its residuals to `φ v`
(`Foundations/OpenContracts`). The queries are a predicate `Q` on nodes.

* `Reach parents Q`: the nodes reachable from the queries through proof parents;
* `reach_parent` ("Reachability soundness"): every proof parent of a reachable node is reachable;
* `reach_min` (`lem:reach-min`): a set containing `Q` and closed under proof parents contains `Reach Q`;
* `reach_union` ("Union law"): `Reach (Q₁ ∪ Q₂) = Reach Q₁ ∪ Reach Q₂`;
* `InFront`: a formula is in the frontier when it is a residual of a reachable node;
  `front_of_reachable`, `front_only_reachable` (`thm:least-frontier`): every residual of a reachable rule
  occurs in the frontier, and every frontier formula is attached to a reachable node;
* `frontier_sufficient`: for an acyclic graph (a rank that decreases along proof parents), any context
  deriving every frontier formula derives the exported formula of every reachable node, in particular of
  every query. This is the compilation of the graph relative to its residual frontier.

These are statements about iPRA derivability proved in the Lean metatheory; no graph is encoded in iPRA.
-/

namespace LeanProofs.IPRA.Foundations.ReachableFrontier

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.OpenContracts (Contract)
open scoped Fm

variable {α : Type} {n : ℕ}

/-- The nodes reachable from the queries through proof parents. -/
inductive Reach (parents : α → List α) (Q : α → Prop) : α → Prop
  | query {v : α} : Q v → Reach parents Q v
  | parent {v p : α} : Reach parents Q v → p ∈ parents v → Reach parents Q p

section Reachability

variable {parents : α → List α} {Q Q₁ Q₂ : α → Prop}

/-- "Reachability soundness": every proof parent used by a reachable node is reachable. -/
theorem reach_parent {v p : α} (h : Reach parents Q v) (hp : p ∈ parents v) : Reach parents Q p :=
  .parent h hp

/-- `lem:reach-min`: `Reach Q` is the least set containing `Q` and closed under proof parents. -/
theorem reach_min {S : α → Prop} (hQ : ∀ v, Q v → S v)
    (hS : ∀ v p, S v → p ∈ parents v → S p) : ∀ v, Reach parents Q v → S v := by
  intro v h
  induction h with
  | query hq => exact hQ _ hq
  | parent _ hp ih => exact hS _ _ ih hp

theorem reach_mono (h : ∀ v, Q₁ v → Q₂ v) : ∀ v, Reach parents Q₁ v → Reach parents Q₂ v :=
  reach_min (fun v hv => .query (h v hv)) (fun _ _ hv hp => .parent hv hp)

/-- "Union law": `Reach (Q₁ ∪ Q₂) = Reach Q₁ ∪ Reach Q₂`. -/
theorem reach_union (v : α) :
    Reach parents (fun u => Q₁ u ∨ Q₂ u) v ↔ Reach parents Q₁ v ∨ Reach parents Q₂ v := by
  constructor
  · refine reach_min (S := fun u => Reach parents Q₁ u ∨ Reach parents Q₂ u) ?_ ?_ v
    · intro u hu
      exact hu.elim (fun h => .inl (.query h)) (fun h => .inr (.query h))
    · intro u p hu hp
      exact hu.elim (fun h => .inl (.parent h hp)) (fun h => .inr (.parent h hp))
  · intro h
    exact h.elim (reach_mono (fun _ h => .inl h) v) (reach_mono (fun _ h => .inr h) v)

end Reachability

/-! ## The residual frontier -/

section Frontier

variable (parents : α → List α) (resid : α → List (Fm PTm n)) (Q : α → Prop)

/-- A formula is in the frontier when it is a residual of a reachable node. -/
def InFront (r : Fm PTm n) : Prop := ∃ v, Reach parents Q v ∧ r ∈ resid v

variable {parents resid Q}

/-- `thm:least-frontier`, first half: every residual of a reachable local rule occurs in the frontier. -/
theorem front_of_reachable {v : α} (hv : Reach parents Q v) {r : Fm PTm n} (hr : r ∈ resid v) :
    InFront parents resid Q r :=
  ⟨v, hv, hr⟩

/-- `thm:least-frontier`, second half: a frontier formula is attached to a reachable node. -/
theorem front_only_reachable {r : Fm PTm n} (h : InFront parents resid Q r) :
    ∃ v, Reach parents Q v ∧ r ∈ resid v :=
  h

/-- The frontier of a union of query sets is the union of the frontiers. -/
theorem front_union {Q₁ Q₂ : α → Prop} (r : Fm PTm n) :
    InFront parents resid (fun u => Q₁ u ∨ Q₂ u) r ↔
      InFront parents resid Q₁ r ∨ InFront parents resid Q₂ r := by
  constructor
  · rintro ⟨v, hv, hr⟩
    exact ((reach_union v).mp hv).elim (fun h => .inl ⟨v, h, hr⟩) (fun h => .inr ⟨v, h, hr⟩)
  · rintro (⟨v, hv, hr⟩ | ⟨v, hv, hr⟩)
    · exact ⟨v, (reach_union v).mpr (.inl hv), hr⟩
    · exact ⟨v, (reach_union v).mpr (.inr hv), hr⟩

/-- The frontier is sufficient: in an acyclic graph whose nodes carry local contracts from their parents'
formulas and their residuals, a context deriving every frontier formula derives the formula of every
reachable node. -/
theorem frontier_sufficient {φ : α → Fm PTm n} (rank : α → ℕ)
    (hrank : ∀ v p, p ∈ parents v → rank p < rank v)
    (hlocal : ∀ v, Contract ((parents v).map φ ++ resid v) (φ v))
    {Δ : List (Fm PTm n)} (hΔ : ∀ r, InFront parents resid Q r → (Δ ⊢[PRAAx] r)) :
    ∀ v, Reach parents Q v → (Δ ⊢[PRAAx] φ v) := by
  have key : ∀ (k : ℕ) (v : α), rank v = k → Reach parents Q v → (Δ ⊢[PRAAx] φ v) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro v hv hr
      refine hlocal v Δ ?_
      intro ψ hψ
      rcases List.mem_append.mp hψ with h₁ | h₂
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h₁
        exact ih (rank p) (lt_of_lt_of_eq (hrank v p hp) hv) p rfl (.parent hr hp)
      · exact hΔ ψ ⟨v, hr, h₂⟩
  exact fun v hr => key (rank v) v rfl hr

end Frontier

end LeanProofs.IPRA.Foundations.ReachableFrontier
