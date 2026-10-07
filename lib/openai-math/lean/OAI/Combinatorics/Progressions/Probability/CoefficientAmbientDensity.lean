import OAI.Combinatorics.Progressions.Geometry.CoefficientAmbientCoordinates

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (f : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → ℝ → ℝ)

noncomputable def coefficientAmbientFactor (s : CoefficientSlot K m) :
    (J s.1 → UnitAddCircle) → ℝ :=
  canonicalAmbientTorusDensity (euclideanSubspace (U s.1)) (b s.1) (o s.1)
    (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => f s.1 i s.2)

noncomputable def coefficientAmbientDensity (v : CoefficientAmbientIndex K J → UnitAddCircle) : ℝ :=
  ∏ s : CoefficientSlot K m,
    coefficientAmbientFactor U b o c w f s (coefficientAmbientSlice s v)

variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
variable (hf : ∀ j i d (k : ℤ), f j i d ((k : ℝ) / basisAxisScale (b j) i) =
  basisAxisScale (b j) i * (p j i d k).toReal)
variable (hs : ∀ j d x, mixedCoefficientDensity (fun i => c j i d) (fun i => w j i d)
  (fun i => p j i d) x ≠ 0 → ∀ a,
    |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) x) a| ≤ 1/4)

include hf hs in
omit [Fintype K] in
theorem coefficientAmbientFactor_eq (s : CoefficientSlot K m) (x : CoefficientTorus (K := K) U) :
    coefficientAmbientFactor U b o c w f s (coefficientAmbientSlice s (coefficientAmbientTorus U x)) =
      canonicalMixedDensity (euclideanSubspace (U s.1)) (b s.1) (hb s.1) (o s.1)
        (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => p s.1 i s.2)
        (euclideanCoefficientEquiv U x s.1 s.2) := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rw [euclideanCoefficientEquiv_mk]
  exact canonicalAmbientTorusDensity_eq (euclideanSubspace (U s.1)) (b s.1) (hb s.1) (o s.1)
    _ _ _ _ (fun i k => hf s.1 i s.2 k) (hs s.1 s.2)
    ((euclideanSubspaceArrayEquiv (U s.1)).symm (fun _ => v s))

include hf hs in
theorem coefficientAmbientDensity_eq (x : CoefficientTorus (K := K) U) :
    coefficientAmbientDensity U b o c w f (coefficientAmbientTorus U x) =
      canonicalCoefficientDensity U b hb o c w p x := by
  unfold coefficientAmbientDensity canonicalCoefficientDensity canonicalArrayDensity
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro d _
  exact coefficientAmbientFactor_eq U b hb o c w f p hf hs ⟨j, d⟩ x

theorem coefficientAmbientDensity_bounds {B L : ℝ≥0} (hB : 1 ≤ B)
    (hcap : ∀ s x, 0 ≤ coefficientAmbientFactor U b o c w f s x ∧
      coefficientAmbientFactor U b o c w f s x ≤ B)
    (hlip : ∀ s, LipschitzWith L (coefficientAmbientFactor U b o c w f s)) :
    (∀ x, 0 ≤ coefficientAmbientDensity U b o c w f x ∧
      coefficientAmbientDensity U b o c w f x ≤ (B : ℝ)^Fintype.card (CoefficientSlot K m)) ∧
    LipschitzWith (Fintype.card (CoefficientSlot K m) * L * B^Fintype.card (CoefficientSlot K m))
      (coefficientAmbientDensity U b o c w f) := by
  have hl (s : CoefficientSlot K m) : LipschitzWith L
      (fun x => coefficientAmbientFactor U b o c w f s (coefficientAmbientSlice s x)) := by
    simpa only [mul_one, Function.comp_def] using (hlip s).comp (coefficientAmbientSlice_lipschitz (J := J) s)
  obtain ⟨hbnd, hlprod⟩ := bounded_lipschitz_real_prod
    (fun s x => coefficientAmbientFactor U b o c w f s (coefficientAmbientSlice s x)) hB hl
    (fun s x => by rw [abs_of_nonneg (hcap s _).1]; exact (hcap s _).2)
  refine ⟨?_, hlprod⟩
  intro x
  have h0 : 0 ≤ coefficientAmbientDensity U b o c w f x :=
    Finset.prod_nonneg (fun s _ => (hcap s _).1)
  exact ⟨h0, (le_abs_self _).trans (hbnd x)⟩

end Erdos3.VectorPolynomial

end

end OAI
