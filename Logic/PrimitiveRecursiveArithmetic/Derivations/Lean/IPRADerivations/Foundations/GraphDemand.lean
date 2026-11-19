import IPRADerivations.Foundations.ReverseDemand
import IPRADerivations.Core.Descent

/-!
# The least reverse demand on an acyclic graph

Packets (`docs/proofs/foundations`): `ipra_kifc_framework_2026-11-15`, `ipra_kifc_framework_2026-11-16`,
`ipra_kifcr_framework_2026-11-16`, `ipra_kifcs_framework_2026-11-16`, Lemma `lem:demand-least` ("Least reverse
demand for an acyclic graph") in full generality: with requests defined backward by

`q_u = max(q_u^terminal, max_{u→v} d_{uv}(q_v))`

for monotone demand transformers, the vector satisfies every terminal and edge inequality and is
componentwise least among all satisfying vectors. (`Foundations/ReverseDemand` is the case of a chain, where
the recursion itself is one primitive recursion.)

The graph is a metalevel object, as in the packets: nodes of a type `α`, the list `succs u` of the targets of
the edges leaving `u`, terminal requests `term u` and edge transformers `d u v` (unary terms). The request
vector is a family of terms `q u`.

* `lub a L`: the maximum of `a` and the terms of the list `L`; `le_lub_base`, `le_lub_mem`, `lub_le`: it is
  their least upper bound;
* `IsDemand`: the defining equations `q u = lub (term u) [d_{uv}(q_v) : v ∈ succs u]` are derivable;
* `sound_term`, `sound_edge`: `term u ≤ q u`, and `d_{uv}(q_v) ≤ q u` for every edge `u → v`;
* `least`: in an acyclic graph (a rank decreasing along edges), for monotone transformers and any vector `p`
  satisfying the terminal and edge inequalities, `q u ≤ p u` for every node `u`.

For a fixed finite graph the terms `q u` are obtained by unfolding the equations in reverse topological
order; that construction is the metalevel elaboration of the packets and is not formalized.
-/

namespace LeanProofs.IPRA.Foundations.GraphDemand

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Ninther (mx)
open LeanProofs.IPRA.Foundations.ReverseDemand (le_mx_left le_mx_right mx_lub)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The maximum of `a` and the members of `L`. -/
def lub (a : PTm n) : List (PTm n) → PTm n
  | [] => a
  | b :: L => mx b (lub a L)

theorem le_lub_base (a : PTm n) : ∀ L : List (PTm n), Γ ⊢[PRAAx] le a (lub a L)
  | [] => le_refl a
  | b :: L => le_trans (le_lub_base a L) (le_mx_right b (lub a L))

theorem le_lub_mem (a : PTm n) : ∀ (L : List (PTm n)) (c : PTm n), c ∈ L → (Γ ⊢[PRAAx] le c (lub a L))
  | [], _, h => nomatch h
  | b :: L, c, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_mx_left _ _
    · exact le_trans (le_lub_mem a L c h') (le_mx_right b (lub a L))

theorem lub_le {a c : PTm n} (ha : Γ ⊢[PRAAx] le a c) :
    ∀ L : List (PTm n), (∀ b ∈ L, Γ ⊢[PRAAx] le b c) → (Γ ⊢[PRAAx] le (lub a L) c)
  | [], _ => ha
  | b :: L, h =>
    mx_lub (h b List.mem_cons_self) (lub_le ha L fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))

section Graph

variable {α : Type} (succs : α → List α) (term : α → PTm n) (d : α → α → PTm 1) (q : α → PTm n)

/-- The defining equations of the reverse demand are derivable. -/
def IsDemand (Γ : List (Fm PTm n)) : Prop :=
  ∀ u, Γ ⊢[PRAAx] q u ≐ lub (term u) ((succs u).map fun v => inst1 (d u v) (q v))

variable {succs term d q}

/-- The terminal inequality `term u ≤ q u`. -/
theorem sound_term (hq : IsDemand succs term d q Γ) (u : α) : Γ ⊢[PRAAx] le (term u) (q u) :=
  le_congr (.eqRefl _) (hq u).eqSymm (le_lub_base _ _)

/-- The edge inequality `d_{uv}(q_v) ≤ q u` for every edge `u → v`. -/
theorem sound_edge (hq : IsDemand succs term d q Γ) {u v : α} (hv : v ∈ succs u) :
    Γ ⊢[PRAAx] le (inst1 (d u v) (q v)) (q u) :=
  le_congr (.eqRefl _) (hq u).eqSymm
    (le_lub_mem _ _ _ (List.mem_map.mpr ⟨v, hv, rfl⟩))

/-- `lem:demand-least`: the reverse demand is componentwise below every satisfying request vector. -/
theorem least (hq : IsDemand succs term d q Γ) (rank : α → ℕ)
    (hrank : ∀ u v, v ∈ succs u → rank v < rank u)
    (hmono : ∀ (u v : α) {a b : PTm n}, (Γ ⊢[PRAAx] le a b) →
      (Γ ⊢[PRAAx] le (inst1 (d u v) a) (inst1 (d u v) b)))
    {p : α → PTm n} (hpt : ∀ u, Γ ⊢[PRAAx] le (term u) (p u))
    (hpe : ∀ u v, v ∈ succs u → (Γ ⊢[PRAAx] le (inst1 (d u v) (p v)) (p u))) :
    ∀ u, Γ ⊢[PRAAx] le (q u) (p u) := by
  have key : ∀ (k : ℕ) (u : α), rank u = k → (Γ ⊢[PRAAx] le (q u) (p u)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro u hu
      refine le_congr (hq u).eqSymm (.eqRefl _) (lub_le (hpt u) _ ?_)
      intro b hb
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
      exact le_trans (hmono u v (ih (rank v) (lt_of_lt_of_eq (hrank u v hv) hu) v rfl)) (hpe u v hv)
  exact fun u => key (rank u) u rfl

end Graph

end LeanProofs.IPRA.Foundations.GraphDemand
