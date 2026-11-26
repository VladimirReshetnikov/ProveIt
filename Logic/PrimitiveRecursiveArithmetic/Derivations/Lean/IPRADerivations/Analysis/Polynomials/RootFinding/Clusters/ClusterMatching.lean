import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm

/-!
# Coverage gives Hall's inequalities, and a bounded matching of enclosures

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `paper/sections/06_clusters.tex`:

* `coverage_hall` (`lem:coverage-hall`): the slots are the points `x_t` of a complete coverage, slot `t` on the
  first side belongs to the cluster `α(t)` and its copy on the second side to the cluster `β(t)`, and clusters
  `i`, `j` are adjacent when `d(a_i, b_j) ≤ δ`; since "`d(a_{α(t)}, b_{β(t)}) ≤ d(a_{α(t)}, x_t) +
  d(x_t, b_{β(t)}) ≤ δ`", every slot is adjacent to its own copy, so `S ⊆ 𝒩(S)` and `|S| ≤ |𝒩(S)|` ("the argument
  does not choose a matching between occurrences");
* `matching_or_violator` (`thm:bounded-matching`): an `N` by `N` bipartite graph has either a perfect matching (a
  permutation `σ` with every `t` adjacent to `σ t`) or a set `S` with `|𝒩(S)| < |S|`;
* `cluster_matching`: under complete coverage the enclosures have a permutation matching all of whose pairs are
  adjacent, that is, at distance at most `δ = ε_A + ε_B`.
-/

namespace LeanProofs.IPRA.Analysis.ClusterMatching

open Finset

variable {T I J : Type*} [Fintype T] [DecidableEq T]

/-- The neighbours of one first-side slot: the second-side slots of adjacent clusters. -/
def adj (A : I → J → Prop) [∀ i j, Decidable (A i j)] (α : T → I) (β : T → J) (t : T) : Finset T :=
  univ.filter fun u => A (α t) (β u)

/-- The neighbours `𝒩(S)` of a set of first-side slots. -/
def nbrs (A : I → J → Prop) [∀ i j, Decidable (A i j)] (α : T → I) (β : T → J) (S : Finset T) : Finset T :=
  S.biUnion (adj A α β)

/-- `lem:coverage-hall`: every slot is adjacent to its own copy, so `|S| ≤ |𝒩(S)|`. -/
theorem coverage_hall (A : I → J → Prop) [∀ i j, Decidable (A i j)] (α : T → I) (β : T → J)
    (hcov : ∀ t, A (α t) (β t)) (S : Finset T) : S.card ≤ (nbrs A α β S).card :=
  card_le_card fun t ht => mem_biUnion.mpr ⟨t, ht, mem_filter.mpr ⟨mem_univ t, hcov t⟩⟩

/-- `thm:bounded-matching`: a perfect matching or a Hall violator. -/
theorem matching_or_violator {N : ℕ} (adj : Fin N → Finset (Fin N)) :
    (∃ σ : Equiv.Perm (Fin N), ∀ t, σ t ∈ adj t) ∨ ∃ S : Finset (Fin N), (S.biUnion adj).card < S.card := by
  by_cases h : ∀ S : Finset (Fin N), S.card ≤ (S.biUnion adj).card
  · left
    obtain ⟨f, hf, hfa⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective adj).mp h
    exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), hfa⟩
  · right
    push_neg at h
    exact h

/-- Under complete coverage the slots have a permutation matching with every pair adjacent. -/
theorem cluster_matching {N : ℕ} {I J : Type*} (A : I → J → Prop) [∀ i j, Decidable (A i j)]
    (α : Fin N → I) (β : Fin N → J) (hcov : ∀ t, A (α t) (β t)) :
    ∃ σ : Equiv.Perm (Fin N), ∀ t, A (α t) (β (σ t)) := by
  rcases matching_or_violator (adj A α β) with ⟨σ, hσ⟩ | ⟨S, hS⟩
  · exact ⟨σ, fun t => (mem_filter.mp (hσ t)).2⟩
  · exact absurd (coverage_hall A α β hcov S) (not_le.mpr hS)

end LeanProofs.IPRA.Analysis.ClusterMatching
