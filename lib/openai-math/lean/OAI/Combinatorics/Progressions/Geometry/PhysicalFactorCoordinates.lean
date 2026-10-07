import OAI.Combinatorics.Progressions.Estimates.PhysicalSingleSiteAmbient

namespace OAI

section

namespace Erdos3.VectorPolynomial
variable {X : Type*} {m : ℕ} {J : Fin m → Type*}

noncomputable def physicalMaskedFactorInput (period : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (t : X → ℝ) :
    (JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle) :=
  ((fun a => (eval t (p a.1) a.2.2 : UnitAddCircle)),
    (fun a => ((eval t (p a.1) a.2 / period : ℝ) : UnitAddCircle)))

noncomputable def physicalGridFactorInput (period : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (t : X → ℝ) :
    (Σ j, J j) → UnitAddCircle :=
  fun a => ((eval t (p a.1) a.2 / period : ℝ) : UnitAddCircle)

end Erdos3.VectorPolynomial

end

end OAI
