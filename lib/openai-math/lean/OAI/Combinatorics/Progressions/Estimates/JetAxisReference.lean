import OAI.Combinatorics.Progressions.Geometry.JetAxisCoordinates

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} (O I : Fin m → Type*) (n : Fin m → ℕ)
variable [∀ j, Fintype (O j)] [∀ j, Fintype (I j)]

theorem coefficientJetAxisEquiv_measurePreserving :
    MeasurePreserving (coefficientJetAxisEquiv O I n)
      (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j)))
      (Measure.pi (coefficientJetAxisReference O)) := by
  let laws := coefficientJetAxisReference (I := I) (n := n) O
  have hinner (j : Fin m) : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi
        (fun a : I j ⊕ Fin (n j) => CoefficientJetAxisRow O ⟨j, a⟩)).symm
      (mixedArrayReference (I j) (Fin (n j)) (O j))
      (Measure.pi (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)) := by
    have hc : (Measure.pi (fun _ : Fin (n j) => (Measure.count : Measure (O j → ℤ)))) =
        Measure.count := pi_count_measure
    have h := measurePreserving_sumPiEquivProdPi_symm
      (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)
    change MeasurePreserving _
      ((Measure.pi (fun _ : I j => (volume : Measure (O j → ℝ)))).prod
        (Measure.pi (fun _ : Fin (n j) => (Measure.count : Measure (O j → ℤ))))) _ at h
    rw [hc] at h
    change MeasurePreserving _
      ((volume : Measure (I j → O j → ℝ)).prod
        (Measure.count : Measure (Fin (n j) → O j → ℤ))) _
    rw [volume_pi]
    exact h
  have houter := measurePreserving_pi
    (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))
    (fun j => Measure.pi (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)) hinner
  have hflat : MeasurePreserving
      (MeasurableEquiv.piCurry
        (fun j (a : I j ⊕ Fin (n j)) => CoefficientJetAxisRow O ⟨j, a⟩)).symm
      (Measure.pi (fun j => Measure.pi (fun a : I j ⊕ Fin (n j) => laws ⟨j, a⟩)))
      (Measure.pi laws) :=
    ⟨(MeasurableEquiv.piCurry
      (fun j (a : I j ⊕ Fin (n j)) => CoefficientJetAxisRow O ⟨j, a⟩)).symm.measurable,
      sigmaFiniteProductMeasure_flatten laws⟩
  exact hflat.comp houter

def coefficientJetAxisSplit (P : LayerSamplerAxis I n → Prop) [DecidablePred P] :
    (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ≃ᵐ
      (∀ a : {a // P a}, CoefficientJetAxisRow O a.val) ×
        (∀ a : {a // ¬P a}, CoefficientJetAxisRow O a.val) :=
  (coefficientJetAxisEquiv O I n).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (CoefficientJetAxisRow O) P)

theorem coefficientJetAxisSplit_measurePreserving
    (P : LayerSamplerAxis I n → Prop) [DecidablePred P] :
    MeasurePreserving (coefficientJetAxisSplit O I n P)
      (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j)))
      ((Measure.pi (fun a : {a // P a} => coefficientJetAxisReference O a.val)).prod
        (Measure.pi (fun a : {a // ¬P a} => coefficientJetAxisReference O a.val))) :=
  (measurePreserving_piEquivPiSubtypeProd (coefficientJetAxisReference O) P).comp
    (coefficientJetAxisEquiv_measurePreserving O I n)

end Erdos3.VectorPolynomial

end

end OAI
