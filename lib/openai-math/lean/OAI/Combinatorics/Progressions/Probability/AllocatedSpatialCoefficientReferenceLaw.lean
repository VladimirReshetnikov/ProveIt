import OAI.Combinatorics.Progressions.Lattices.AllocatedCoefficientIntegerMarginal
import OAI.Combinatorics.Progressions.Lattices.CoefficientDeckResidueMask

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

def coefficientIntegerDeckChartResidues {K : Type*} {m : ℕ}
    {n : Fin m → ℕ} {E : Fin m → Type*} (q : ℕ)
    (a : CoefficientIntegerScalarIndex K n → ℤ)
    (deck : CoefficientDeckResidues (K := K) E q) :
    CoefficientChartResidues K n E q :=
  fun j e => Sum.elim (fun i => (a ⟨j,e,i⟩ : ZMod q)) (deck j e)

theorem coefficientIntegerDeckChartResidues_sampler {K : Type*} {m : ℕ}
    {I E : Fin m → Type*} {n : Fin m → ℕ} (q : ℕ)
    (a : CoefficientSamplerArrays (K := K) I n)
    (deck : CoefficientDeckResidues (K := K) E q) :
    coefficientIntegerDeckChartResidues q (coefficientIntegerScalars a) deck =
      coefficientSamplerChartResidues q a deck := rfl

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedSpatialCoefficientReferenceLaw
    {X : Type*} [Fintype X] (q : ℕ) [NeZero q]
    (spatial : PMF (Option (LayerSamplerVariables G I n B) × X → ℤ))
    (deck : PMF (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q))
    (event : ((Option (LayerSamplerVariables G I n B) × X) → ZMod q) →
      CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop) :
    (∑' z, (spatial z).toReal *
      ∫ a : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
          CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q,
        (if event (fun v => (z v : ZMod q)) (coefficientSamplerChartResidues q a.1 a.2)
          then (1 : ℝ) else 0)
        ∂(allocatedCoefficientSource B U b hR hσ S).prod deck.toMeasure) =
    ((spatial.bind fun z => (allocatedCoefficientIntegerPMF B U b hR hσ S).bind
      fun a => deck.map fun r => decide
        (event (fun v => (z v : ZMod q)) (coefficientIntegerDeckChartResidues q a r))) true).toReal := by
  rw [pmf_bind_toReal]
  apply tsum_congr
  intro z
  congr 1
  exact allocatedCoefficientSource_integer_prod_indicator B U b hR hσ S deck
    (fun a r => event (fun v => (z v : ZMod q)) (coefficientIntegerDeckChartResidues q a r))

end Erdos3.VectorPolynomial

end

end OAI
