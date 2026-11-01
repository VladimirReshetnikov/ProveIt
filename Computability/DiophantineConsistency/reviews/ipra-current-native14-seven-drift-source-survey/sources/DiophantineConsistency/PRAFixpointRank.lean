import Foundation.FirstOrder.Arithmetic.HFS.Fixpoint
/-! # Stage bounds for fixpoints with a decreasing rank

Foundation's `Fixpoint.Construction.fixpoint_iff` bounds the stage of a
fixpoint element by `x + 1` when the construction is `StrongFinite`: the core
only queries members below `x`. Recursion graphs (formula, term and vector
recursions) are not strong-finite in that sense; e.g. for the bound-variable
count, `bv (∀ p) = bv p - 1`, so the queried entry `⟪0, p, y + 1⟫` of
`⟪0, ∀ p, y⟫` can be larger.

They are strong-finite for a suitable *rank* `ρ` with `x ≤ ρ x`: every member
the core queries has strictly smaller rank (`RankFinite`). Then every fixpoint
element lies in the stage `ρ x + 1` (`mem_limSeq_rank`), by induction on the
rank value, cumulativity of the stages and monotonicity of the core: the same
argument as Foundation's `mem_limSeq_self`, which is the case `ρ = id`. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAFixpointRank
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {k : ℕ} {φ : Fixpoint.Blueprint k} (c : Fixpoint.Construction V φ)

/-- The core only queries members of strictly smaller rank. -/
def RankFinite (ρ : V → V) : Prop :=
  ∀ (v : Fin k → V) (C : Set V) (x : V), c.Φ v C x → c.Φ v {z | z ∈ C ∧ ρ z < ρ x} x

variable {c}

/-- **Every fixpoint element lies in the stage `ρ x + 1`.** -/
theorem mem_limSeq_rank (ρ : V → V) [hρ : 𝚺₁-Function₁ ρ] (hge : ∀ x, x ≤ ρ x)
    (hr : RankFinite c ρ) (v : Fin k → V) :
    ∀ u s, u ∈ c.limSeq v s → u ∈ c.limSeq v (ρ u + 1) := by
  have key : ∀ n u, u ≤ n → ρ u = n → ∀ s, u ∈ c.limSeq v s → u ∈ c.limSeq v (n + 1) := by
    intro n
    induction n using ISigma1.pi1_order_induction
    · apply HierarchySymbol.Definable.all
      apply HierarchySymbol.Definable.imp (by definability)
      apply HierarchySymbol.Definable.imp (by definability)
      apply HierarchySymbol.Definable.all
      apply HierarchySymbol.Definable.imp
      · apply HierarchySymbol.Definable.comp₂
          ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> #1 :> fun i ↦ &(v i)),
            by intro v; simp [c.eval_limSeqDef]⟩
          (by definability)
      · apply HierarchySymbol.Definable.comp₂
          ⟨φ.limSeqDef.rew <| Rew.embSubsts (#0 :> ‘#3 + 1’ :> fun i ↦ &(v i)),
            by intro v; simp [c.eval_limSeqDef]⟩
          (by definability)
    case ind n ih =>
      intro u hun hρu s hu
      rcases zero_or_succ s with (rfl | ⟨s, rfl⟩)
      · simp at hu
      rcases c.mem_limSeq_succ_iff.mp hu with ⟨_, Hu⟩
      have h1 : c.Φ v {z | z ∈ c.limSeq v s ∧ ρ z < ρ u} u := hr v _ u Hu
      have h2 : c.Φ v {z | z ∈ c.limSeq v n} u :=
        c.monotone (by
          simp only [Set.setOf_subset_setOf, and_imp]
          intro z hz hzr
          have hzn : ρ z < n := hρu ▸ hzr
          have hz' := ih (ρ z) hzn z (hge z) rfl s hz
          exact c.limSeq_cumulative (succ_le_iff_lt.mpr hzn) hz')
          h1
      exact c.mem_limSeq_succ_iff.mpr ⟨hun, h2⟩
  intro u s hu
  exact key (ρ u) u (hge u) rfl s hu

/-- **Fixpoint membership by stage `ρ x + 1`.** -/
theorem fixpoint_iff_rank (ρ : V → V) [𝚺₁-Function₁ ρ] (hge : ∀ x, x ≤ ρ x)
    (hr : RankFinite c ρ) (v : Fin k → V) (x : V) :
    c.Fixpoint v x ↔ x ∈ c.limSeq v (ρ x + 1) :=
  ⟨fun ⟨s, hs⟩ => mem_limSeq_rank ρ hge hr v x s hs, fun h => ⟨_, h⟩⟩

end DiophantineConsistency.PRAFixpointRank
