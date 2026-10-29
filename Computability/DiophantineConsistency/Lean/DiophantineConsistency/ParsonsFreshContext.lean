import DiophantineConsistency.ParsonsAllInvert
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsFreshContext
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsAllInvert

theorem keep_prefix {L : Language} (A : Semiproposition L 1) (t : SyntacticTerm L)
    (Γ : Sequent L) {Δ Ξ : Sequent L} (hs : Selection A t Δ Ξ) :
    Selection A t (Γ ++ Δ) (Γ ++ Ξ) := by
  induction Γ with
  | nil => exact hs
  | cons φ Γ ih => exact .keep φ ih

/-- Open a selected universal occurrence after an arbitrary prefix, without
permuting or contracting the original cut-free derivation. -/
theorem fresh_open_at {L : Language} (A B : Semiproposition L 1)
    (u : SyntacticTerm L) (Γ Δ : Sequent L)
    (d : Derivation (B/[u] :: (Γ ++ (∀⁰ A) :: Δ))) (hc : Derivation.IsCutFree d) :
    ∃ e : Derivation (Rewriting.shift (B/[u]) :: (Γ⁺ ++ A.free :: Δ⁺)),
      Derivation.IsCutFree e ∧ e.height < d.exs.height := by
  let f : ℕ → SyntacticTerm L := fun x => &(x+1)
  have hr : Rew.rewrite f = (@Rew.shift L 0) := by ext i <;> simp [f]
  have heq : (B/[u] :: (Γ ++ (∀⁰ A) :: Δ)).map (Rew.rewrite f ▹ ·) =
      Rewriting.shift (B/[u]) :: (Γ⁺ ++ (∀⁰ (Rew.shift ▹ A)) :: Δ⁺) := by
    simp [Rewriting.shifts, hr]
  let hd := (d.rewrite f).cast heq
  have hf : Derivation.IsCutFree hd := by
    simp only [hd, Derivation.IsCutFree.cast, Derivation.isCutFree_rewrite_iff_isCutFree]
    exact hc
  have hh : hd.height = d.height := by
    simp only [hd, Derivation.height_cast]
    exact height_rewrite d f
  obtain ⟨e, he, hb⟩ := invert hd hf (Rew.shift ▹ A) (&0)
    (.keep _ (keep_prefix _ _ Γ⁺ (.replace (same _ _ Δ⁺))))
  have heq' : (Rewriting.shift (B/[u]) :: (Γ⁺ ++ (Rew.shift ▹ A)/[&0] :: Δ⁺)) =
      (Rewriting.shift (B/[u]) :: (Γ⁺ ++ A.free :: Δ⁺)) := by simp
  refine ⟨e.cast heq', ?_, ?_⟩
  · simpa using he
  · simp only [Derivation.height_cast, Derivation.height_exs]
    omega
end DiophantineConsistency.ParsonsFreshContext
