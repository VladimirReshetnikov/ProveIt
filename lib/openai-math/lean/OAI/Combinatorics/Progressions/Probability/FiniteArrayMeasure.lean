import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem finiteArray_uncurry_measurePreserving {I J X : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] (μ : I → J → Measure X) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.curry I J X).symm
      (Measure.pi (fun i => Measure.pi (μ i))) (Measure.pi (fun ij : I × J => μ ij.1 ij.2)) := by
  refine ⟨(MeasurableEquiv.curry I J X).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (MeasurableEquiv.curry I J X).symm.measurable (MeasurableSet.univ_pi hs)]
  have he : (MeasurableEquiv.curry I J X).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext x
    constructor
    · intro hx i _ j _
      exact hx (i, j) (Set.mem_univ _)
    · intro hx ij _
      exact hx ij.1 (Set.mem_univ _) ij.2 (Set.mem_univ _)
  rw [he, Measure.pi_pi]
  simp only [Measure.pi_pi, Fintype.prod_prod_type]

def finiteArrayTranspose (I J X : Type*) [MeasurableSpace X] : (I → J → X) ≃ᵐ (J → I → X) :=
  ((MeasurableEquiv.curry I J X).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : J × I => X) (Equiv.prodComm I J))).trans
      (MeasurableEquiv.curry J I X)

theorem finiteArrayTranspose_apply {I J X : Type*} [MeasurableSpace X]
    (x : I → J → X) (j : J) (i : I) : finiteArrayTranspose I J X x j i = x i j := rfl

theorem finiteArrayTranspose_measurePreserving {I J X : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace X] (μ : I → J → Measure X) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (finiteArrayTranspose I J X)
      (Measure.pi (fun i => Measure.pi (μ i))) (Measure.pi (fun j => Measure.pi (fun i => μ i j))) := by
  have h₁ := finiteArray_uncurry_measurePreserving μ
  have h₂ := measurePreserving_piCongrLeft (fun ji : J × I => μ ji.2 ji.1) (Equiv.prodComm I J)
  have h₃ := (finiteArray_uncurry_measurePreserving (fun j i => μ i j)).symm
    (MeasurableEquiv.curry J I X).symm
  exact h₃.comp (h₂.comp h₁)

end Erdos3

end

end OAI
