/-
  CLASS EMBEDDINGS: NO INTERNAL UNBOUNDED PART OF THE RANGE (synthesis §11, report R3).

  For `j : V → M` and a regular `θ` with `j θ = θ`, the known stationary-partition
  analysis (Hamkins–Kirmayer–Perlmutter; synthesis Lemma 11.1) provides a set `T ⊆ θ`
  that `M` regards as stationary — so it meets the closure set of every function
  `θ → θ` belonging to `M` — but that is disjoint from the closure club
  `C_j = {β < θ : j '' β ⊆ β}`.  That published lemma is taken as a hypothesis here.

  * `le_of_strictMonoOn_Iio`: an increasing map on `θ` satisfies `ξ ≤ b ξ`;
  * `no_internal_unbounded_range` (Theorem 11.2): no strictly increasing `f ∈ M` has its
    values in `j '' θ`; equivalently no unbounded subset of `j '' θ` is enumerated in `M`.

  Nothing is admitted in this file.
-/
import Cardinals.Combinatorics.Ordinals

universe u

namespace Cardinals.Range

open Ordinal Set OrdinalLemmas

/-- A strictly increasing map defined below `θ` dominates the identity. -/
theorem le_of_strictMonoOn_Iio (θ : Ordinal.{u}) (b : Ordinal.{u} → Ordinal.{u})
    (hb : ∀ ξ η, ξ < η → η < θ → b ξ < b η) : ∀ ξ < θ, ξ ≤ b ξ := by
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ ih =>
    intro hξ
    by_contra hlt
    rw [not_le] at hlt
    have h1 := ih (b ξ) hlt (hlt.trans hξ)
    have h2 := hb (b ξ) ξ hlt hξ
    exact absurd h1 (not_le.mpr h2)

/-- **No internal unbounded part of the range (synthesis Theorem 11.2).**

* `j` is the action of the embedding on the ordinals below the fixed regular `θ`;
* `InM f` says that the function `f : θ → θ` belongs to `M`;
* `T` is `M`-stationary (`hstat`) and disjoint from the closure club of `j` (`hdisj`):
  this is the published stationary-partition lemma, with `T = T_κ`;
* `f ∈ M` is strictly increasing with all its values in `j '' θ` — for instance the
  increasing enumeration of an unbounded `A ∈ M` with `A ⊆ j '' θ`.

These assumptions are contradictory. -/
theorem no_internal_unbounded_range (θ : Ordinal.{u}) (j : Ordinal.{u} → Ordinal.{u})
    (hj : ∀ ξ η, ξ < η → η < θ → j ξ < j η)
    (InM : (Ordinal.{u} → Ordinal.{u}) → Prop) (T : Set Ordinal.{u})
    (hstat : ∀ f, InM f → ∃ β ∈ closurePoints θ f, β ∈ T)
    (hdisj : ∀ β ∈ closurePoints θ j, β ∉ T)
    (f : Ordinal.{u} → Ordinal.{u}) (hfM : InM f)
    (hf : ∀ ξ η, ξ < η → η < θ → f ξ < f η)
    (hrange : ∀ ξ < θ, ∃ ζ < θ, f ξ = j ζ) : False := by
  classical
  -- the preimage enumeration `b`, with `f ξ = j (b ξ)`
  choose! b hbθ hbf using hrange
  have hjmono : ∀ ξ η, ξ ≤ η → η < θ → j ξ ≤ j η := by
    intro ξ η hle hη
    rcases hle.lt_or_eq with h | h
    · exact (hj ξ η h hη).le
    · rw [h]
  have hbmono : ∀ ξ η, ξ < η → η < θ → b ξ < b η := by
    intro ξ η hξη hη
    by_contra hge
    rw [not_lt] at hge
    have h1 := hjmono (b η) (b ξ) hge (hbθ ξ (hξη.trans hη))
    rw [← hbf ξ (hξη.trans hη), ← hbf η hη] at h1
    exact absurd (hf ξ η hξη hη) (not_lt.mpr h1)
  have hid := le_of_strictMonoOn_Iio θ b hbmono
  have hdom : ∀ ξ < θ, j ξ ≤ f ξ :=
    enum_dominates θ j f b hjmono (fun ξ hξ => ⟨hid ξ hξ, hbθ ξ hξ⟩) hbf
  exact no_dominating_function θ j f T hdisj (hstat f hfM) hdom

/-- **Corollary (synthesis Corollary 11.3, first half).**  If `M` contains, together with
each of its unbounded sets `B ⊆ θ`, the increasing enumerations of the final segments of
`B`, then every such `B` has unboundedly many elements outside `j '' θ`.  We state the
contrapositive core: a final segment of `B` lying inside `j '' θ` is impossible as soon as
its enumeration is in `M`. -/
theorem final_segment_not_in_range (θ : Ordinal.{u}) (j : Ordinal.{u} → Ordinal.{u})
    (hj : ∀ ξ η, ξ < η → η < θ → j ξ < j η)
    (InM : (Ordinal.{u} → Ordinal.{u}) → Prop) (T : Set Ordinal.{u})
    (hstat : ∀ f, InM f → ∃ β ∈ closurePoints θ f, β ∈ T)
    (hdisj : ∀ β ∈ closurePoints θ j, β ∉ T)
    (f : Ordinal.{u} → Ordinal.{u}) (hfM : InM f)
    (hf : ∀ ξ η, ξ < η → η < θ → f ξ < f η) :
    ∃ ξ < θ, ∀ ζ < θ, f ξ ≠ j ζ := by
  by_contra hcon
  push Not at hcon
  exact no_internal_unbounded_range θ j hj InM T hstat hdisj f hfM hf hcon

end Cardinals.Range
