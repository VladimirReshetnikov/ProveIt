import OAI.Combinatorics.Progressions.Linear.AnchoredKernelInvariance

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def refilteredReconstructionMap (a : ι)
    (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) :
    let H := (pi D).filtration.gradedRefiltrationSubalgebra W
    H →ₗ⁅ℚ⁆ (H ⧸ ((pi D).filtration.gradedRefiltration W).layerIdeal s) ×
      (∀ i : {i : ι // i ≠ a}, L i.val) :=
  (lieQuotientMap (((pi D).filtration.gradedRefiltration W).layerIdeal s)).prod
    (liePiMap (fun i : {i : ι // i ≠ a} =>
      (liePiEval i.val).comp ((pi D).filtration.gradedRefiltrationSubalgebra W).incl))

theorem refilteredReconstructionMap_real_kernel (a : ι)
    (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
    (x : ℝ ⊗[ℚ] (pi D).filtration.gradedRefiltrationSubalgebra W) :
    realificationLieHom (refilteredReconstructionMap D a W) x = 0 ↔
      realificationLieHom ((pi D).filtration.gradedRefiltrationSubalgebra W).incl x ∈
        (pi D).filtration.realGradedRefiltrationLayer W s ∧
      ∀ i, i ≠ a → realificationLieHom (liePiEval i)
        (realificationLieHom ((pi D).filtration.gradedRefiltrationSubalgebra W).incl x) = 0 := by
  classical
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I := ((pi D).filtration.gradedRefiltration W).layerIdeal s
  let other := liePiMap (fun i : {i : ι // i ≠ a} => (liePiEval i.val).comp H.incl)
  have hquot : realificationLieHom (lieQuotientMap I) x = 0 ↔
      realificationLieHom H.incl x ∈ (pi D).filtration.realGradedRefiltrationLayer W s := by
    change I.toSubmodule.mkQ.baseChange ℝ x = 0 ↔ _
    rw [realification_mkQ_eq_zero_iff]
    exact (pi D).filtration.mem_native_refiltration_layer W s x
  have hcomp (i : ι) : realificationLieHom ((liePiEval i).comp H.incl) x =
      realificationLieHom (liePiEval i) (realificationLieHom H.incl x) := by
    change (((liePiEval i).toLinearMap.comp H.incl.toLinearMap).baseChange ℝ) x = _
    rw [LinearMap.baseChange_comp]
    rfl
  have hother : realificationLieHom other x = 0 ↔
      ∀ i, i ≠ a → realificationLieHom (liePiEval i) (realificationLieHom H.incl x) = 0 := by
    rw [realification_liePiMap_eq_zero_iff (fun i : {i : ι // i ≠ a} => (D i.val).basis)]
    constructor
    · intro h i hi
      exact (hcomp i) ▸ h ⟨i, hi⟩
    · intro h i
      exact (hcomp i.val).symm ▸ h i.val i.property
  have hpair := realification_prod_eq_zero_iff (lieQuotientMap I).toLinearMap other.toLinearMap x
  exact hpair.trans (and_congr hquot hother)

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

theorem exists_native_refiltered_quotient_orbits {L σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L (s + 1))
    (W : LieSubalgebra ℚ F.AssociatedGraded) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hzero : coefficients p 0 = 0) :
    ∃ (q : (F.gradedRefiltration W).realification.PolynomialOrbit w)
      (qbar : (F.gradedRefiltration W).quotientTop.realification.PolynomialOrbit w),
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        q.log = p ∧ coefficients q.log 0 = 0 ∧ DegreeLE w s qbar.log ∧
      ∀ x, (F.gradedRefiltration W).quotientTop.realification.polynomialOrbitEval w x qbar =
        (F.gradedRefiltration W).realQuotientStepHom
          ((F.gradedRefiltration W).layerIdeal (s + 1)) le_rfl
          ((F.gradedRefiltration W).realification.polynomialOrbitEval w x q) := by
  obtain ⟨q, hq, hz⟩ := F.exists_native_refiltered_orbit W w hw p hp hzero
  let qbar := (F.gradedRefiltration W).realQuotientPolynomialOrbit
    ((F.gradedRefiltration W).layerIdeal (s + 1)) (t := s) le_rfl q
  exact ⟨q, qbar, hq, hz, qbar.degreeLE, fun x =>
    (F.gradedRefiltration W).realQuotientPolynomialOrbit_eval
      ((F.gradedRefiltration W).layerIdeal (s + 1)) le_rfl q x⟩

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem anchored_reconstruction_frozen_invariant {J : Type*} [Fintype J]
    {L : (Bool ⊕ (J × Bool)) → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
    {s : ℕ} {d : (Bool ⊕ (J × Bool)) → ℕ}
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
    (eta : J → L (.inl true) →ₗ[ℚ] ℚ) (theta : J → L (.inl false) →ₗ[ℚ] ℚ)
    (alpha : ∀ j, L (.inr (j, true)) →ₗ[ℚ] ℚ) (beta : ∀ j, L (.inr (j, false)) →ₗ[ℚ] ℚ)
    (hfrequency : ∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W s →
      realifyFunctional (piFrequency
        (selectedOrbitFrequencies (anchoredFrequencyData eta theta alpha beta j) (anchoredInputs j))) x = 0)
    (S : (D (.inl true)).Space → ℂ)
    (hinvariant : ∀ z, z ∈ (D (.inl true)).filtration.realification.subgroup s →
      (∀ j, realifyFunctional (eta j) z.coord = 0) → ∀ x, S (z • x) = S x)
    (E R b : (pi D).RealGroup) (z : ((pi D).filtration.gradedRefiltration W).realification.Group)
    (hz : realificationLieHom (refilteredReconstructionMap D (.inl true) W) z.coord = 0) :
    let z' := NilpotentLieBCHGroup.realificationMap
      (hnil := ((pi D).filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
      (hM := (pi D).filtration.lowerCentralSeries_eq_bot)
      ((pi D).filtration.gradedRefiltrationSubalgebra W).incl z
    S (QuotientGroup.mk (productProjectionHom D (.inl true) (E * (z' * b) * R))) =
      S (QuotientGroup.mk (productProjectionHom D (.inl true) (E * b * R))) := by
  obtain ⟨htop, hother⟩ := (refilteredReconstructionMap_real_kernel D (.inl true) W z.coord).mp hz
  apply anchored_frozen_observable_invariant D W eta theta alpha beta hfrequency S hinvariant
    E R b _ htop
  intro i hi
  apply NilpotentLieBCHGroup.ext
  exact hother i hi

end Erdos3.RationalFilteredNilmanifold

end

end OAI
