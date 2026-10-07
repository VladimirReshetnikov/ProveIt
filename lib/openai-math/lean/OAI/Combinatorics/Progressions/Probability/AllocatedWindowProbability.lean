import Mathlib.Probability.Distributions.Uniform
import OAI.Combinatorics.Progressions.Sampling.AllocatedGridNaturalWindow
import OAI.Combinatorics.Progressions.Sampling.AllocatedProbabilityGrid

namespace OAI

section

namespace Erdos3

open scoped Classical

theorem finset_indicator_eq_card_mul_uniform {X : Type*} (W : Finset X)
    (hW : W.Nonempty) (z : X) :
    (W : Set X).indicator (fun _ => (1 : ℝ)) z =
      (W.card : ℝ) * (PMF.uniformOfFinset W hW z).toReal := by
  by_cases hz : z ∈ W
  · rw [Set.indicator_of_mem hz, PMF.uniformOfFinset_apply_of_mem hW hz]
    have hc : (W.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hW)
    simp [ENNReal.toReal_inv, hc]
  · rw [Set.indicator_of_notMem hz, PMF.uniformOfFinset_apply_of_notMem hW hz]
    simp

end Erdos3

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

noncomputable def allocatedGridWindowPMF
    (selected : {a // grid a} → Prop) [DecidablePred selected]
    (W : ∀ a : {a // grid a}, Finset (CoefficientJetAxisRow O a.val))
    (p : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    (hW : ∀ a, selected a → (W a).Nonempty) (a : {a // grid a}) :
    PMF (CoefficientJetAxisRow O a.val) :=
  if h : selected a then PMF.uniformOfFinset (W a) (hW a h) else p a

omit [∀ j, Fintype (O j)] in
theorem allocatedGridWindowFactor_eq_probability
    (selected : {a // grid a} → Prop) [DecidablePred selected]
    (W : ∀ a : {a // grid a}, Finset (CoefficientJetAxisRow O a.val))
    (p : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    (hW : ∀ a, selected a → (W a).Nonempty)
    (a : {a // grid a}) (z : CoefficientJetAxisRow O a.val) :
    allocatedGridWindowFactor B U b S O selected W p a z =
      (if selected a then ((W a).card : ℝ) else 1) *
        (allocatedGridWindowPMF B U b S O selected W p hW a z).toReal := by
  by_cases hs : selected a
  · simp only [allocatedGridWindowFactor, allocatedGridWindowPMF, hs, ↓reduceDIte, ↓reduceIte]
    exact finset_indicator_eq_card_mul_uniform (W a) (hW a hs) z
  · simp only [allocatedGridWindowFactor, allocatedGridWindowPMF, hs, ↓reduceDIte, ↓reduceIte, one_mul]

omit [∀ j, Fintype (O j)] in
theorem allocatedGridWindowWeight_eq_probability
    (selected : {a // grid a} → Prop) [DecidablePred selected]
    (W : ∀ a : {a // grid a}, Finset (CoefficientJetAxisRow O a.val))
    (p : ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val))
    (hW : ∀ a, selected a → (W a).Nonempty)
    (z : AllocatedFrozenJetRows B U b S O) :
    allocatedGridWindowWeight B U b S O selected W p z =
      (∏ a : {a // grid a}, if selected a then ((W a).card : ℝ) else 1) *
        allocatedProbabilityGridDensity B U b S
          (allocatedGridWindowPMF B U b S O selected W p hW) z := by
  simp only [allocatedGridWindowWeight,
    allocatedGridWindowFactor_eq_probability B U b S O selected W p hW,
    Finset.prod_mul_distrib, allocatedProbabilityGridDensity]

end Erdos3.VectorPolynomial

end

end OAI
