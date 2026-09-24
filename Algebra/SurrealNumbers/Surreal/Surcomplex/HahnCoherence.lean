import Surreal.Surcomplex.AlgebraicallyClosed
import Surreal.Foundations.SignSequenceHahnCoherence

/-!
# Coherent complex Hahn workspaces

Splitting a complex Hahn series into real and imaginary coordinates commutes
with embedding its exponents. The corresponding actual surcomplex value is
therefore unchanged by enlargement of the small exponent workspace.
-/

universe u v w

namespace Surreal

noncomputable section

variable {Γ : Type v} {Δ : Type w}
  [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]

namespace HahnSeries

/-- Real and imaginary Hahn coordinates commute with exponent embedding. -/
theorem workspaceEmbedding_realComplexHahnEquiv (e : Γ →+ Δ) (he : StrictMono e)
    (z : Complexify (_root_.HahnSeries Γ ℝ)) :
    workspaceEmbedding e he (realComplexHahnEquiv z) =
      realComplexHahnEquiv ⟨workspaceEmbedding e he z.re, workspaceEmbedding e he z.im⟩ := by
  apply _root_.HahnSeries.ext
  funext b
  by_cases hb : b ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hb
    simp only [workspaceEmbedding_coeff, coeff_realComplexHahnEquiv]
  · simp only [workspaceEmbedding_coeff_of_not_mem_range e he _ hb,
      coeff_realComplexHahnEquiv]
    rfl

end HahnSeries

namespace Surcomplex

open Foundations

variable [Small.{u} Γ] [Small.{u} Δ]

/-- Enlarging an exponent workspace does not change actual surcomplex evaluation. -/
theorem hahnEmbedding_workspaceEmbedding (e : Γ →+ Δ) (he : StrictMono e)
    (d : Δ →+ SignSequence.{u}) (hd : StrictMono d) (x : _root_.HahnSeries Γ ℂ) :
    hahnEmbedding d hd (HahnSeries.workspaceEmbedding e he x) =
      hahnEmbedding (d.comp e) (hd.comp he) x := by
  obtain ⟨z, rfl⟩ := HahnSeries.realComplexHahnEquiv.surjective x
  rw [HahnSeries.workspaceEmbedding_realComplexHahnEquiv,
    hahnEmbedding_realComplexHahnEquiv, hahnEmbedding_realComplexHahnEquiv]
  apply ext
  · exact SignSequence.hahnEmbedding_workspaceEmbedding e he d hd z.re
  · exact SignSequence.hahnEmbedding_workspaceEmbedding e he d hd z.im

/-- The coherence identity also holds for the complete actual ring maps. -/
theorem hahnEmbedding_comp_workspaceEmbedding (e : Γ →+ Δ) (he : StrictMono e)
    (d : Δ →+ SignSequence.{u}) (hd : StrictMono d) :
    (hahnEmbedding d hd).comp (HahnSeries.workspaceEmbedding e he).toRingHom =
      hahnEmbedding (d.comp e) (hd.comp he) := by
  apply RingHom.ext
  intro x
  exact hahnEmbedding_workspaceEmbedding e he d hd x

end Surcomplex

end

end Surreal
