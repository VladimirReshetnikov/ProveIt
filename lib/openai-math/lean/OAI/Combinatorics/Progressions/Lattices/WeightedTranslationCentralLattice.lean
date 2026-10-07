import OAI.Combinatorics.Progressions.Fourier.WeightedTranslationBufferedCentralFrequency
import OAI.Combinatorics.Progressions.Lattices.CentralLatticeQuotientAction

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
variable {σ : Type*} [Fintype σ]

noncomputable def centralRationalElement (w : σ → ℕ) (d : ℕ) (hd : 0 < d)
    (q : ℚ) : weightedSubalgebra w d :=
  ⟨⟨0, C q⟩, ⟨by simp, (monomial_mem_restrictSupport ℚ).mpr
    (Or.inl (by simpa using hd))⟩⟩

noncomputable def centralRationalLine (w : σ → ℕ) (d : ℕ) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d) (q : ℚ) : (weightedFiltration w d hwd).Group :=
  ⟨centralRationalElement w d hd q⟩

@[simp] theorem bchTranslationHom_centralRationalLine (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d) (hwd : ∀ i, w i ≤ d) (q : ℚ) :
    bchTranslationHom w d hw hwd (centralRationalLine w d hd hwd q) = ⟨0, C q⟩ := by
  change PolynomialTranslationGroup.exponentialElement 0 (C q) = _
  apply PolynomialTranslationGroup.ext
  · rfl
  · exact polynomialExponentialCoordinate_C 0 q

theorem centralRationalLine_mem_lattice (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d) (hwd : ∀ i, w i ≤ d) (n : ℤ) :
    centralRationalLine w d hd hwd (n : ℚ) ∈ weightedTranslationLattice w d hwd := by
  rw [weightedTranslationLattice_eq_integral_preimage w d hw hwd]
  change bchTranslationHom w d hw hwd _ ∈ PolynomialTranslationGroup.integralGroup
  rw [bchTranslationHom_centralRationalLine]
  exact (PolynomialTranslationGroup.mem_integralGroup_iff _).mpr
    ⟨fun _ => ⟨0, by simp⟩, integerCoefficientPolynomials_C n⟩

@[simp] theorem bchRealTranslationHom_realification_centralRationalLine
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d) (q : ℚ) :
    bchRealTranslationHom w d hwd (NilpotentLieBCHGroup.realificationHom
      (centralRationalLine w d hd hwd q)) = ⟨0, C (q : ℝ)⟩ := by
  rw [bchRealTranslationHom_rational w d hw hwd, bchTranslationHom_centralRationalLine]
  apply PolynomialTranslationGroupOver.ext
  · funext i
    change algebraMap ℚ ℝ 0 = 0
    exact map_zero _
  · change MvPolynomial.map (algebraMap ℚ ℝ) (C q) = C (q : ℝ)
    simp

theorem realification_centralRationalLine_mem_realLattice
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)] (n : ℤ) :
    NilpotentLieBCHGroup.realificationHom (centralRationalLine w d hd hwd (n : ℚ)) ∈
      (weightedTranslationNilmanifold w d hw hwd).realLattice :=
  ⟨_, centralRationalLine_mem_lattice w d hw hd hwd n, rfl⟩

theorem centralRealLine_rat (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d) (hwd : ∀ i, w i ≤ d) (q : ℚ) :
    centralRealLine w d hw hd hwd (q : ℝ) =
      NilpotentLieBCHGroup.realificationHom (centralRationalLine w d hd hwd q) := by
  apply bchRealTranslationHom_injective w d hwd
  rw [centralRealLine_map, bchRealTranslationHom_realification_centralRationalLine w d hw hd hwd q]

theorem centralRealLine_int_mem_realLattice
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)] (n : ℤ) :
    centralRealLine w d hw hd hwd (n : ℝ) ∈
      (weightedTranslationNilmanifold w d hw hwd).realLattice := by
  have h := realification_centralRationalLine_mem_realLattice w d hw hd hwd n
  rw [← centralRealLine_rat] at h
  simpa only [Rat.cast_intCast] using h

theorem centralRealLine_mem_realLattice_iff
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)] (t : ℝ) :
    centralRealLine w d hw hd hwd t ∈
      (weightedTranslationNilmanifold w d hw hwd).realLattice ↔
      ∃ n : ℤ, t = (n : ℝ) := by
  constructor
  · rintro ⟨g, hg, he⟩
    have hgi : bchTranslationHom w d hw hwd g ∈ PolynomialTranslationGroup.integralGroup := by
      have hg' : g ∈ weightedTranslationLattice w d hwd := hg
      rw [weightedTranslationLattice_eq_integral_preimage w d hw hwd] at hg'
      exact hg'
    have hp := ((PolynomialTranslationGroup.mem_integralGroup_iff _).mp hgi).2
    obtain ⟨n, hn⟩ := (mem_integerCoefficientPolynomials_iff _).mp hp 0
    have he' := congrArg (bchRealTranslationHom w d hwd) he
    rw [bchRealTranslationHom_rational w d hw hwd, centralRealLine_map] at he'
    have hc := congrArg (fun x : PolynomialTranslationGroupOver ℝ σ => x.polynomial.coeff 0) he'
    change (MvPolynomial.map (algebraMap ℚ ℝ)
      (bchTranslationHom w d hw hwd g).polynomial).coeff 0 = (C t).coeff 0 at hc
    rw [coeff_map, hn] at hc
    exact ⟨n, by simpa using hc.symm⟩
  · rintro ⟨n, rfl⟩
    exact centralRealLine_int_mem_realLattice w d hw hd hwd n

theorem centralRealLine_int_smul
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)] (n : ℤ)
    (x : (weightedTranslationNilmanifold w d hw hwd).Space) :
    centralRealLine w d hw hd hwd (n : ℝ) • x = x :=
  central_lattice_smul_eq _ _ (centralRealLine_int_mem_realLattice w d hw hd hwd n)
    (fun g => (centralRealLine_commute w d hw hd hwd n g).eq) x

theorem centralRealLine_add_int_smul
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)] (t : ℝ) (n : ℤ)
    (x : (weightedTranslationNilmanifold w d hw hwd).Space) :
    centralRealLine w d hw hd hwd (t + n) • x = centralRealLine w d hw hd hwd t • x :=
  central_lattice_int_add_smul_eq _ _ (centralRealLine_add w d hw hd hwd)
    (centralRealLine_int_mem_realLattice w d hw hd hwd)
    (fun n g => (centralRealLine_commute w d hw hd hwd n g).eq) t n x

theorem centralRealLine_smul_eq_iff
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)] (t : ℝ)
    (x : (weightedTranslationNilmanifold w d hw hwd).Space) :
    centralRealLine w d hw hd hwd t • x = x ↔ ∃ n : ℤ, t = (n : ℝ) := by
  induction x using Quotient.inductionOn' with
  | h g =>
    change (QuotientGroup.mk (centralRealLine w d hw hd hwd t * g) :
      (weightedTranslationNilmanifold w d hw hwd).Space) = QuotientGroup.mk g ↔ _
    rw [(centralRealLine_commute w d hw hd hwd t g).eq, QuotientGroup.eq]
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, Subgroup.inv_mem_iff] using
      centralRealLine_mem_realLattice_iff w d hw hd hwd t

end Erdos3.PolynomialTranslationLie

end

end OAI
