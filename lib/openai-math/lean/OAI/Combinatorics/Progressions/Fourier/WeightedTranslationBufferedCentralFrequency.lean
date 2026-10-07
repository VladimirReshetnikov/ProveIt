import OAI.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

noncomputable def centralConstantPolynomial (w : σ → ℕ) (d : ℕ) (hd : 0 < d)
    (t : ℝ) : weightedSupportLT (R := ℝ) w d :=
  ⟨C t, (monomial_mem_restrictSupport ℝ).mpr (Or.inl (by simpa using hd))⟩

noncomputable def centralRealLine (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) (t : ℝ) :
    (weightedFiltration w d hwd).realification.Group :=
  ⟨polynomialRealElement w d hw (centralConstantPolynomial w d hd t)⟩

@[simp] theorem centralRealLine_map (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) (t : ℝ) :
    bchRealTranslationHom w d hwd (centralRealLine w d hw hd hwd t) = ⟨0, C t⟩ :=
  bchRealTranslationHom_pure_polynomial_of_shape w d hwd _ _
    (polynomialRealElement_shear_base w d hw _)
    (polynomialRealElement_shear_extra w d hw _)

@[simp] theorem centralRealLine_zero (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) :
    centralRealLine w d hw hd hwd 0 = 1 := by
  apply bchRealTranslationHom_injective w d hwd
  simp only [centralRealLine_map, map_one, map_zero]
  rfl

@[simp] theorem centralRealLine_add (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) (t u : ℝ) :
    centralRealLine w d hw hd hwd (t + u) =
      centralRealLine w d hw hd hwd t * centralRealLine w d hw hd hwd u := by
  apply bchRealTranslationHom_injective w d hwd
  simp only [map_mul, centralRealLine_map]
  apply PolynomialTranslationGroupOver.ext <;> simp

 theorem centralRealLine_commute (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) (t : ℝ)
    (g : (weightedFiltration w d hwd).realification.Group) :
    Commute (centralRealLine w d hw hd hwd t) g := by
  apply bchRealTranslationHom_injective w d hwd
  simp only [map_mul, centralRealLine_map]
  apply PolynomialTranslationGroupOver.ext <;> simp [add_comm]

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

theorem weightedTranslationBufferedObservable_central
    (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (t : ℝ)
    (q : (weightedTranslationNilmanifold w d hw hwd).Space) :
    weightedTranslationBufferedObservable w d hw hwd Ψ D₀
      (centralRealLine w d hw hd hwd t • q) =
    weightedTranslationBufferedObservable w d hw hwd Ψ D₀ q *
      (Real.fourierChar t : ℂ) := by
  induction q using Quotient.inductionOn with
  | h g =>
    change weightedTranslationBufferedObservable w d hw hwd Ψ D₀
      (QuotientGroup.mk (centralRealLine w d hw hd hwd t * g)) = _
    rw [(centralRealLine_commute w d hw hd hwd t g).eq]
    simp only [weightedTranslationBufferedObservable_mk, map_mul, centralRealLine_map]
    exact bufferedTranslationPhase_central Ψ D₀ _ t

end Erdos3.PolynomialTranslationLie

end

end OAI
