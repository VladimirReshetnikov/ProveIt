import DiophantineConsistency.ParsonsAllInvert
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsFreshOpen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ParsonsAllInvert

theorem fresh_open {L : Language} (A B : Semiproposition L 1)
    (u : SyntacticTerm L) (Γ : Sequent L)
    (d : Derivation (B/[u] :: (∀⁰ A) :: Γ)) (hc : Derivation.IsCutFree d) :
    ∃ e : Derivation (Rewriting.shift (B/[u]) :: A.free :: Γ⁺),
      Derivation.IsCutFree e ∧ e.height < d.exs.height := by
  let f : ℕ → SyntacticTerm L := fun x => &(x+1)
  have hr : Rew.rewrite f = (@Rew.shift L 0) := by ext i <;> simp [f]
  have heq : (B/[u] :: (∀⁰ A) :: Γ).map (Rew.rewrite f ▹ ·) =
      Rewriting.shift (B/[u]) :: (∀⁰ (Rew.shift ▹ A)) :: Γ⁺ := by
    simp [Rewriting.shifts, hr]
  let hd := (d.rewrite f).cast heq
  have hf : Derivation.IsCutFree hd := by
    simp only [hd, Derivation.IsCutFree.cast, Derivation.isCutFree_rewrite_iff_isCutFree]
    exact hc
  have hh : hd.height = d.height := by
    simp only [hd, Derivation.height_cast]
    exact height_rewrite d f
  obtain ⟨e, he, hb⟩ := invert hd hf (Rew.shift ▹ A) (&0)
    (.keep _ (.replace (same _ _ Γ⁺)))
  have heq' : (Rewriting.shift (B/[u]) :: (Rew.shift ▹ A)/[&0] :: Γ⁺) =
      (Rewriting.shift (B/[u]) :: A.free :: Γ⁺) := by simp
  refine ⟨e.cast heq', ?_, ?_⟩
  · simpa using he
  · simp only [Derivation.height_cast, Derivation.height_exs]
    omega
end DiophantineConsistency.ParsonsFreshOpen
