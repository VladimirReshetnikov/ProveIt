import DiophantineConsistency.ParsonsRule
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsSide
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule
variable {L : Language} [L.ORing]

theorem base_sigma (φ : Semiproposition L 1) (h : Hierarchy 𝚺 1 φ) :
    Hierarchy 𝚺 1 (base φ) := by
  simpa [base] using h

theorem step_pi_two (φ : Semiproposition L 1) (h : Hierarchy 𝚺 1 φ) :
    Hierarchy 𝚷 2 (step φ) := by
  have hp : Hierarchy 𝚷 2 φ := h.strict_mono _ (by decide)
  have hs : Hierarchy 𝚺 2 φ := h.mono (by decide)
  simpa [step, Semiformula.imp_eq] using And.intro hs hp

theorem side_complexities (φ : Semiproposition L 1) (E : Proposition L)
    (t : SyntacticTerm L) (hφ : Hierarchy 𝚺 1 φ) (hE : Hierarchy 𝚺 1 E) :
    Hierarchy 𝚷 2 (base φ ⋎ E) ∧ Hierarchy 𝚷 2 (step φ ⋎ E) ∧
      Hierarchy 𝚷 2 (∼(φ/[t]) ⋎ E) := by
  have he : Hierarchy 𝚷 2 E := hE.strict_mono _ (by decide)
  have hb : Hierarchy 𝚷 2 (base φ) := (base_sigma φ hφ).strict_mono _ (by decide)
  have hn : Hierarchy 𝚷 2 (∼(φ/[t])) := (Hierarchy.neg (Hierarchy.rew (Rew.subst ![t]) hφ)).mono (by decide)
  exact ⟨(Hierarchy.or_iff).2 ⟨hb, he⟩, (Hierarchy.or_iff).2 ⟨step_pi_two φ hφ, he⟩,
    (Hierarchy.or_iff).2 ⟨hn, he⟩⟩
end DiophantineConsistency.ParsonsSide
