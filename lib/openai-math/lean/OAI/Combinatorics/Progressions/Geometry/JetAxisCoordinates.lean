import OAI.Combinatorics.Progressions.Estimates.CoefficientJetScalar
import OAI.Combinatorics.Progressions.Estimates.CoveredMixedArrayImage

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (O I : Fin m → Type*) (n : Fin m → ℕ)

def coefficientJetAxisEquiv :
    (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) ≃ᵐ
      (∀ a : LayerSamplerAxis I n, CoefficientJetAxisRow O a) :=
  (MeasurableEquiv.piCongrRight (fun j =>
    (MeasurableEquiv.sumPiEquivProdPi (fun a : I j ⊕ Fin (n j) => CoefficientJetAxisRow O ⟨j, a⟩)).symm)).trans
      (MeasurableEquiv.piCurry (fun j (a : I j ⊕ Fin (n j)) => CoefficientJetAxisRow O ⟨j, a⟩)).symm

theorem coefficientJetAxisEquiv_real (x) (j : Fin m) (i : I j) :
    coefficientJetAxisEquiv O I n x ⟨j, Sum.inl i⟩ = (x j).1 i := rfl

theorem coefficientJetAxisEquiv_integer (x) (j : Fin m) (i : Fin (n j)) :
    coefficientJetAxisEquiv O I n x ⟨j, Sum.inr i⟩ = (x j).2 i := rfl

theorem canonicalCoefficientJetArrays_axis {α K : Type*} [DecidableEq α] [Fintype K]
    (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
    (x : CoefficientSamplerArrays (K := K) I n) (a : LayerSamplerAxis I n) :
    coefficientJetAxisEquiv O I n (canonicalCoefficientJetArrays root A rows x) a =
      coefficientJetAxisMap (fun j => boundedCoefficientJetMatrix root A (j.val + 1) (rows j)) a
        (coefficientAxisEquiv K I n x a) := by
  rcases a with ⟨j, i | i⟩ <;> rfl

end Erdos3.VectorPolynomial

end

end OAI
