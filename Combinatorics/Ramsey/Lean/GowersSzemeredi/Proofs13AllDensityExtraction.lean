import GowersSzemeredi.Proofs13DenseEdgeModels
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! This module keeps `lemma_13_6_from_initial_stages_at`; the rest of the
development, with its description, is in `Proofs13AllDensityExtractionSide`,
outside the final route. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **Stage 13.6 at a general precision**, at all densities. -/
theorem lemma_13_6_from_initial_stages_at {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N) (m : Nat) (eps : Real)
    (h134 : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D)
    (h135 : IsStage135Data S D E)
    (hprec : ∀ i, ∀ h, h ∈ E.Q.carrier →
      (centeredAbs ((D.a i * h + D.b i) * E.Q.step) : Real) ≤ eps * N)
    (hm : 0 < m) (hsize : m * m ≤ N) (hupper : m + 1 ≤ E.Q.length)
    (hlower : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ m)
    (hbudget : eps ≤ section10Zeta (S.alpha ^ 32 / 16) / m) :
    ∃ F : Stage136Data N, IsStage136Data S D E F ∧ m ≤ F.R.length ∧ F.R.length ≤ E.Q.length := by
  classical
  have hex (h : ZMod N) (hh : h ∈ criticalHeights S D E) :=
    section13_uniform_height_model_all_densities S h (Finset.mem_filter.mp hh).2
  choose! Y psi hdata using hex
  refine lemma_13_6_of_bohr_models_at S _ _ eps D E m Y _ psi h134 h135 hprec hm hsize hupper
    hlower (fun h hh ↦ ⟨(hdata h hh).1, (hdata h hh).2.1⟩) (fun h _ r hr ↦ ?_) hbudget
    (fun h hh ↦ (hdata h hh).2.2)
  rw [← section13_vertical_fibre_function, sq, ← mul_assoc]
  exact (Finset.mem_filter.mp hr).2

end LeanProofs.GowersSzemeredi
