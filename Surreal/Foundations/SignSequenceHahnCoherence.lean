import Surreal.Foundations.SignSequenceHahnEmbedding

/-!
# Coherence of actual Hahn evaluation under workspace enlargement

Embedding exponents into a larger small workspace and then evaluating gives
the same actual surreal value as evaluating along the composite exponent
map. The proof compares all formal coefficients, including exponents outside
the image; it places no finite-support restriction on the series.
-/

universe u v w

namespace Surreal.Foundations

noncomputable section

variable {Γ : Type v} {Δ : Type w}
  [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
  [Small.{u} Γ] [Small.{u} Δ]

namespace SmallNormalForm

/-- Formal coefficient embedding commutes with enlargement of the exponent workspace. -/
theorem hahnEmbedding_workspaceEmbedding (e : Γ →+ Δ) (he : StrictMono e)
    (d : Δ →+ SignSequence.{u}) (hd : StrictMono d) (x : _root_.HahnSeries Γ ℝ) :
    hahnEmbedding d hd (Surreal.HahnSeries.workspaceEmbedding e he x) =
      hahnEmbedding (d.comp e) (hd.comp he) x := by
  apply ext
  intro b
  by_cases hb : b ∈ Set.range (fun a : Γ => -(d.comp e) a)
  · obtain ⟨a, rfl⟩ := hb
    rw [coeff_hahnEmbedding]
    change coeff (hahnEmbedding d hd (Surreal.HahnSeries.workspaceEmbedding e he x))
      (-d (e a)) = _
    rw [coeff_hahnEmbedding, Surreal.HahnSeries.workspaceEmbedding_coeff]
  · rw [coeff_hahnEmbedding_of_not_mem_range (d.comp e) (hd.comp he) x hb]
    by_cases hb' : b ∈ Set.range (fun a : Δ => -d a)
    · obtain ⟨a, rfl⟩ := hb'
      rw [coeff_hahnEmbedding]
      apply Surreal.HahnSeries.workspaceEmbedding_coeff_of_not_mem_range
      rintro ⟨c, rfl⟩
      exact hb ⟨c, rfl⟩
    · exact coeff_hahnEmbedding_of_not_mem_range d hd _ hb'

end SmallNormalForm

namespace SignSequence

/-- Actual evaluation is unchanged by passing to a larger exponent workspace. -/
theorem hahnEmbedding_workspaceEmbedding (e : Γ →+ Δ) (he : StrictMono e)
    (d : Δ →+ SignSequence.{u}) (hd : StrictMono d) (x : _root_.HahnSeries Γ ℝ) :
    hahnEmbedding d hd (Surreal.HahnSeries.workspaceEmbedding e he x) =
      hahnEmbedding (d.comp e) (hd.comp he) x := by
  rw [hahnEmbedding_apply, SmallNormalForm.hahnEmbedding_workspaceEmbedding,
    hahnEmbedding_apply]

/-- Workspace coherence as an equality of actual ring homomorphisms. -/
theorem hahnEmbedding_comp_workspaceEmbedding (e : Γ →+ Δ) (he : StrictMono e)
    (d : Δ →+ SignSequence.{u}) (hd : StrictMono d) :
    (hahnEmbedding d hd).comp (Surreal.HahnSeries.workspaceEmbedding e he).toRingHom =
      hahnEmbedding (d.comp e) (hd.comp he) := by
  apply RingHom.ext
  intro x
  exact hahnEmbedding_workspaceEmbedding e he d hd x

end SignSequence

end

end Surreal.Foundations
