import OAI.Combinatorics.Progressions.Fourier.ControlledFrequencyExternalTransfer

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped Classical

theorem exists_nativePresentPivotQuotient_budget :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L M J : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {s d e r : ℕ} (D : RationalFilteredNilmanifold L s d)
      (b : Basis (Fin e) ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
      (eta : J → L →ₗ[ℚ] ℚ) (code : Fin r → Option J) (p : ℝ),
      1 ≤ s → 0 ≤ p → D.GeometryComplexityLE p → (e : ℝ) ≤ p → (r : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (b.repr (φ (D.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (eta i (D.basis j)) ≤ p) →
      let ideal := D.filtration.pivotAnnihilatorIdeal φ
        (fun k => eta (kernelProjectionSelectedPivot code k))
        (Finset.univ : Finset (KernelProjectionPresentPivot code)).toList
      let hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule := by
        rw [D.filtration.terminal]; exact bot_le
      ∃ n : ℕ, n ≤ d ∧ ∃ Q : RationalFilteredNilmanifold (L ⧸ ideal) s n,
        Q.filtration = D.filtration.quotientLie ideal hI ∧
        Q.lattice = D.lattice.map (D.filtration.quotientStepHom ideal hI) ∧
        Q.GeometryComplexityLE ((p + 2) ^ C) ∧
        ∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap ideal (D.basis j)) i) ≤
          (p + 2) ^ C := by
  obtain ⟨a, _ha, hspan⟩ := exists_nativeTopMarkKernel_spanning_budget
  obtain ⟨bexp, _hb, hquotient⟩ := exists_controlled_frequency_quotient_budget
  let X : Polynomial ℕ := Polynomial.X
  let q := X + (X + 2) ^ a + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget ((q + 2) ^ bexp)
  refine ⟨C, hC, ?_⟩
  intro L M J _ _ _ _ s d e r D b φ eta code p hs hp hD he hr hφ heta ideal hI
  let P := D.filtration.layer s ⊓ LinearMap.ker φ.toLinearMap
  obtain ⟨vP, hvP, hvPH⟩ := hspan D b φ p hs hp hD he hφ
  let p₀ := p + (p + 2) ^ a + 1
  have hpa : 0 ≤ (p + 2) ^ a := by positivity
  have hp₀ : 0 ≤ p₀ := by dsimp [p₀]; positivity
  have hpp₀ : p ≤ p₀ := by dsimp [p₀]; linarith
  have hap₀ : (p + 2) ^ a ≤ p₀ := by dsimp [p₀]; linarith
  have hbudget' : (p₀ + 2) ^ bexp ≤ (p + 2) ^ C := by
    simpa [X, q, p₀, Polynomial.eval₂_pow] using hbudget p hp
  have hresult := hquotient D hs P inf_le_left vP hvP eta code p₀ hp₀
    (hD.mono D hpp₀) (hr.trans hpp₀)
    (fun i j => (hvPH i j).trans hap₀) (fun i j => (heta i j).trans hpp₀)
  let K := frequencyCodeKernel P eta code
  let hK : K ≤ D.filtration.layer s := (finiteFrequencyKernel_le P _ _).trans inf_le_left
  let I := D.filtration.topSubspaceIdeal K hK
  have hIdeal : ideal = I := D.filtration.pivotAnnihilatorIdeal_presentPivots φ eta code hK
  revert hI
  rw [hIdeal]
  intro hI
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hmap⟩ := hresult
  exact ⟨n, hn, Q, hQF, hQL, hQ.mono Q hbudget', fun i j => (hmap j i).trans hbudget'⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
