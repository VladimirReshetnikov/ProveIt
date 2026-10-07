import OAI.Combinatorics.Progressions.Linear.DetectedTranslationLogProjectionHeight
import OAI.Combinatorics.Progressions.Polynomial.DetectedTranslationPhaseBudget
import OAI.Combinatorics.Progressions.Polynomial.DetectedTranslationPhaseDegree

namespace OAI

section

namespace Erdos3

noncomputable def detectedTranslationCoordinateConstant (d : ℕ) : ℕ :=
  (exists_detectedTranslationPhase_budget d).choose

theorem detectedTranslationCoordinateConstant_ge_two (d : ℕ) :
    2 ≤ detectedTranslationCoordinateConstant d :=
  (exists_detectedTranslationPhase_budget d).choose_spec.1

namespace PolynomialTranslationLie
open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold
variable {B L : Type} {U ι : Type*} [Fintype B] [Fintype U] [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem detectedTranslationGroupCoordinates_uniform_bounds
    {p : ℝ} (hp : 0 ≤ p)
    (hU : (Fintype.card U : ℝ) ≤ p) (hB : (Fintype.card B : ℝ) ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p)
    (hb : ∀ i j, rationalLogHeight
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).basis.repr (b i) j) ≤ p)
    (T : U → ℝ) (hT : ∀ i, 0 < T i)
    (E Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : U => 1) T (Real.exp p) E)
    (m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp p)
    (hQ : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolRationalGrid
      b ω hN (fun _ : U => 1) m Q) :
    let C := detectedTranslationCoordinateConstant d
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      realPolynomialMass (scaleMvPolynomialAxes (Sum.elim T (fun _ : B => 1))
        (detectedTranslationPhasePolynomial w d hw hwd M hM D E)) ≤ Real.exp ((p + C) ^ C) ∧
      (∀ i, realPolynomialMass (scaleMvPolynomialAxes T
        (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i)) ≤ Real.exp ((p + C) ^ C)) ∧
      realPolynomialCoefficientGrid q (detectedTranslationPhasePolynomial w d hw hwd M hM D Q) ∧
      (∀ i, realPolynomialCoefficientGrid q
        (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D Q i)) := by
  have hκ : (Fintype.card (WeightedBasisIndex w d) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (weightedBasisIndex_card_le_pair_basis w d hw b)).trans hι
  have hproj : ∀ k i, |(detectedTranslationLogProjectionMatrix w d hw b ω k i : ℝ)| ≤ Real.exp p := by
    intro k i
    exact (rational_abs_real_le_numerator _).trans
      ((rationalLogHeight_le_iff _ p).mp
        (detectedTranslationLogProjectionMatrix_logHeight w d hw hwd M hM D b ω hp hb k i)).1
  obtain ⟨q₀, hq₀, hq₀bound, hq₀grid⟩ :=
    exists_detectedTranslationLogCoordinate_grid_of_basis_height w d hw hwd M hM D b ω hN hp hb m hm
  have hbudget := (exists_detectedTranslationPhase_budget d).choose_spec.2
    (Fintype.card U) (Fintype.card (WeightedBasisIndex w d)) (Fintype.card ι)
    (Fintype.card B) m q₀ p (Real.exp p) (Real.exp p) hp hU hκ hι hB
    (Real.exp_pos p).le le_rfl (Real.exp_pos p).le le_rfl hmp hq₀bound
  obtain ⟨hbase, hphase, hden⟩ := hbudget
  refine ⟨d.factorial * q₀ ^ (d + 1), by positivity, hden, ?_, ?_, ?_, ?_⟩
  · have h := detectedTranslationPhasePolynomial_mass_of_slow w d hw hwd M hM D b ω hN T hT
      (Real.exp_pos p).le (Real.exp_pos p).le hproj E hE
    exact h.trans (by simpa only [mul_assoc, detectedTranslationCoordinateConstant] using hphase)
  · intro i
    have h := detectedTranslationBaseCoordinatePolynomial_mass_of_slow w d hw hwd M hM D b ω hN T hT
      (Real.exp_pos p).le (Real.exp_pos p).le hproj E hE i
    exact h.trans (by simpa only [mul_assoc, detectedTranslationCoordinateConstant] using hbase)
  · exact detectedTranslationPhasePolynomial_coefficientGrid w d hw hwd M hM D Q (hq₀grid Q hQ)
  · intro i
    apply realPolynomialCoefficientGrid_mono (show q₀ ∣ d.factorial * q₀ ^ (d + 1) from
      dvd_mul_of_dvd_right (dvd_pow_self q₀ (by omega : d + 1 ≠ 0)) _)
    rw [detectedTranslationBaseCoordinatePolynomial_eq_logCoordinate]
    exact hq₀grid Q hQ (Sum.inl i)

end PolynomialTranslationLie
end Erdos3

end

end OAI
