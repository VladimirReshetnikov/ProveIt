import IPRADerivations.Foundations.ReachableFrontier

/-!
# Query compilation and unreachable extensions

Packet: `foundations/ipra_kifcs_framework_2026-11-16`: Theorem `thm:contract-cut` ("Simultaneous contract
cut", `contract_cut`), Theorem `thm:node-accum` ("Node accumulation"),
Theorem `thm:query-compile` ("Query compilation"), the corollary "Ordinary residual sequent", and Theorem
`thm:dead-code` ("Unreachable extension invariance").

The proof graph is the metalevel object of `Foundations/ReachableFrontier`: nodes, proof parents, exported
formulas `φ v`, residuals, local contracts, a rank decreasing along proof parents, and a query predicate.

* `conj L`: the conjunction of a list of formulas (`0 = 0` for the empty list); `conj_intro`, `conj_elim`;
* `node_accum` (`thm:node-accum`): a context deriving every frontier formula derives the conclusion of
  every reachable node (this is `frontier_sufficient`);
* `query_compile` (`thm:query-compile`, and the residual sequent): it derives the conjunction `Φ_Q` of the
  conclusions of any list of query nodes;
* `reach_agree`, `front_agree` (`thm:dead-code`): if a second graph has the same proof parents and the same
  residuals at every node that is reachable in the first, then the reachable sets and the frontiers of
  the two graphs coincide. Adding nodes that are not backward reachable from the queries therefore
  changes neither, and the compiled query contract has the same interface.

These are statements about iPRA derivability proved in the Lean metatheory; no graph is encoded in iPRA.
-/

namespace LeanProofs.IPRA.Foundations.QueryCompilation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.OpenContracts (Contract)
open LeanProofs.IPRA.Foundations.ReachableFrontier (Reach InFront reach_min frontier_sufficient)
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {α : Type} {n : ℕ}

/-- The conjunction of a list of formulas. -/
def conj : List (Fm PTm n) → Fm PTm n
  | [] => (zero : PTm n) ≐ zero
  | φ :: L => φ ⋏ conj L

theorem conj_intro {Γ : List (Fm PTm n)} :
    ∀ L : List (Fm PTm n), (∀ φ ∈ L, Γ ⊢[PRAAx] φ) → (Γ ⊢[PRAAx] conj L)
  | [], _ => Prf.eqRefl zero
  | φ :: L, h =>
    Prf.andI (h φ List.mem_cons_self) (conj_intro L fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))

theorem conj_elim {Γ : List (Fm PTm n)} :
    ∀ L : List (Fm PTm n), (Γ ⊢[PRAAx] conj L) → ∀ φ ∈ L, Γ ⊢[PRAAx] φ
  | [], _, _, h => nomatch h
  | ψ :: L, hc, φ, h => by
    have hc' : Γ ⊢[PRAAx] ψ ⋏ conj L := hc
    rcases List.mem_cons.mp h with rfl | h'
    · exact Prf.andE₁ hc'
    · exact conj_elim L (Prf.andE₂ hc') φ h'

/-- `thm:contract-cut` ("Simultaneous contract cut"): `Contract A φ` and a contract from `B` for every member
of `A` give `Contract B φ`. -/
theorem contract_cut {A B : List (Fm PTm n)} {φ : Fm PTm n} (c : Contract A φ)
    (s : ∀ ψ ∈ A, Contract B ψ) : Contract B φ :=
  fun Δ k => c Δ fun ψ hψ => s ψ hψ Δ k

section Graph

variable {parents : α → List α} {resid : α → List (Fm PTm n)} {Q : α → Prop} {φ : α → Fm PTm n}

/-- `thm:node-accum`: every reachable node has its conclusion from the frontier. -/
theorem node_accum (rank : α → ℕ) (hrank : ∀ v p, p ∈ parents v → rank p < rank v)
    (hlocal : ∀ v, Contract ((parents v).map φ ++ resid v) (φ v))
    {Δ : List (Fm PTm n)} (hΔ : ∀ r, InFront parents resid Q r → (Δ ⊢[PRAAx] r)) :
    ∀ v, Reach parents Q v → (Δ ⊢[PRAAx] φ v) :=
  frontier_sufficient rank hrank hlocal hΔ

/-- `thm:query-compile`: the conjunction of the conclusions of the queries from the frontier. -/
theorem query_compile (rank : α → ℕ) (hrank : ∀ v p, p ∈ parents v → rank p < rank v)
    (hlocal : ∀ v, Contract ((parents v).map φ ++ resid v) (φ v))
    {Δ : List (Fm PTm n)} (hΔ : ∀ r, InFront parents resid Q r → (Δ ⊢[PRAAx] r))
    (qs : List α) (hqs : ∀ q ∈ qs, Q q) : Δ ⊢[PRAAx] conj (qs.map φ) :=
  conj_intro _ fun ψ hψ => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hψ
    exact frontier_sufficient rank hrank hlocal hΔ q (.query (hqs q hq))

end Graph

/-! ## Unreachable extensions -/

/-- `thm:dead-code`: graphs that agree on the proof parents of the nodes reachable in the first have the
same reachable nodes. -/
theorem reach_agree {parents₁ parents₂ : α → List α} {Q : α → Prop}
    (h : ∀ v, Reach parents₁ Q v → parents₂ v = parents₁ v) (v : α) :
    Reach parents₂ Q v ↔ Reach parents₁ Q v := by
  constructor
  · refine reach_min (S := Reach parents₁ Q) (fun u hu => .query hu) ?_ v
    intro u p hu hp
    rw [h u hu] at hp
    exact .parent hu hp
  · intro hv
    have key : Reach parents₁ Q v ∧ Reach parents₂ Q v := by
      refine reach_min (S := fun u => Reach parents₁ Q u ∧ Reach parents₂ Q u)
        (fun u hu => ⟨.query hu, .query hu⟩) ?_ v hv
      rintro u p ⟨h₁, h₂⟩ hp
      refine ⟨.parent h₁ hp, .parent h₂ ?_⟩
      rw [h u h₁]
      exact hp
    exact key.2

/-- `thm:dead-code`: if moreover the residuals agree there, the frontiers coincide. -/
theorem front_agree {parents₁ parents₂ : α → List α} {resid₁ resid₂ : α → List (Fm PTm n)} {Q : α → Prop}
    (h : ∀ v, Reach parents₁ Q v → parents₂ v = parents₁ v)
    (hr : ∀ v, Reach parents₁ Q v → resid₂ v = resid₁ v) (r : Fm PTm n) :
    InFront parents₂ resid₂ Q r ↔ InFront parents₁ resid₁ Q r := by
  constructor
  · rintro ⟨v, hv, hm⟩
    have hv₁ := (reach_agree h v).mp hv
    refine ⟨v, hv₁, ?_⟩
    rw [← hr v hv₁]
    exact hm
  · rintro ⟨v, hv, hm⟩
    refine ⟨v, (reach_agree h v).mpr hv, ?_⟩
    rw [hr v hv]
    exact hm

end LeanProofs.IPRA.Foundations.QueryCompilation
