import OAI.Combinatorics.Progressions.Geometry.FullTaggedChartCoefficientRange

namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {U B I : Type*} [Fintype I]

theorem polynomialTagLinearEmbedding_mass_le (E : B → I → ℝ)
    {L : ℝ} (hE : ∀ b i, |E b i| ≤ L) (j : U ⊕ B) :
    realPolynomialMass (polynomialTagLinearEmbedding E j) ≤
      max 1 ((Fintype.card I : ℝ) * L) := by
  classical
  cases j with
  | inl u =>
      simpa only [polynomialTagLinearEmbedding_inl, realPolynomialMass_X]
        using le_max_left 1 ((Fintype.card I : ℝ) * L)
  | inr b =>
      rw [polynomialTagLinearEmbedding_inr]
      apply (realPolynomialMass_sum_le _ _).trans
      apply le_trans (b := ∑ _i : I, L)
      · apply Finset.sum_le_sum
        intro i _
        exact (realPolynomialMass_C_mul_le _ _).trans
          (by simpa only [realPolynomialMass_X, mul_one] using hE b i)
      · simp

theorem polynomialTagLinearEmbedding_totalDegree_le (E : B → I → ℝ)
    (j : U ⊕ B) : (polynomialTagLinearEmbedding E j).totalDegree ≤ 1 := by
  classical
  cases j with
  | inl u => simp
  | inr b =>
      rw [polynomialTagLinearEmbedding_inr]
      apply totalDegree_finsetSum_le
      intro i _
      exact (totalDegree_mul _ _).trans (by simp)

theorem polynomialTagRestriction_mass_le (E : B → I → ℝ)
    (p : MvPolynomial (U ⊕ B) ℝ) {L : ℝ} {s : ℕ}
    (hE : ∀ b i, |E b i| ≤ L) (hp : p.totalDegree ≤ s) :
    realPolynomialMass (aeval (polynomialTagLinearEmbedding E) p) ≤
      realPolynomialMass p * (max 1 ((Fintype.card I : ℝ) * L)) ^ s :=
  realPolynomialMass_substitution_le p (polynomialTagLinearEmbedding E)
    (le_max_left _ _) (polynomialTagLinearEmbedding_mass_le E hE) hp

theorem polynomialTagRestriction_totalDegree_le (E : B → I → ℝ)
    (p : MvPolynomial (U ⊕ B) ℝ) :
    (aeval (polynomialTagLinearEmbedding E) p).totalDegree ≤ p.totalDegree := by
  change (eval₂Hom C (polynomialTagLinearEmbedding E) p).totalDegree ≤ p.totalDegree
  simpa only [mul_one] using polynomial_substitution_totalDegree_le p
    (polynomialTagLinearEmbedding E) (polynomialTagLinearEmbedding_totalDegree_le E) le_rfl

theorem polynomialTagLinearEmbedding_coefficientGrid (E : B → I → ℝ)
    (d : ℕ) (hE : ∀ b i, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * E b i)
    (j : U ⊕ B) :
    realPolynomialCoefficientGrid d (polynomialTagLinearEmbedding E j) := by
  classical
  cases j with
  | inl u => exact realPolynomialCoefficientGrid_X d _
  | inr b =>
      apply (realPolynomialCoefficientGrid_iff d _).mpr
      change C (d : ℝ) * (∑ i, C (E b i) * X (Sum.inr i)) ∈
        integralRealPolynomialSubring (U ⊕ I)
      rw [Finset.mul_sum]
      apply (integralRealPolynomialSubring (U ⊕ I)).sum_mem
      intro i _
      obtain ⟨z, hz⟩ := hE b i
      rw [← mul_assoc, ← map_mul, ← hz]
      exact (integralRealPolynomialSubring (U ⊕ I)).mul_mem
        (C_int_mem_integralRealPolynomialSubring z) (X_mem_integralRealPolynomialSubring _)

theorem polynomialTagRestriction_coefficientGrid (E : B → I → ℝ)
    (p : MvPolynomial (U ⊕ B) ℝ) (q d s : ℕ)
    (hE : ∀ b i, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * E b i)
    (hp : p.totalDegree ≤ s) (hq : realPolynomialCoefficientGrid q p) :
    realPolynomialCoefficientGrid (q * d ^ s)
      (aeval (polynomialTagLinearEmbedding E) p) :=
  realPolynomialCoefficientGrid_substitute p (polynomialTagLinearEmbedding E)
    q d s hp hq (polynomialTagLinearEmbedding_coefficientGrid E d hE)

theorem polynomialTagRestriction_mass_le_of_coeff_le [Fintype U] [Fintype B]
    (E : B → I → ℝ) (p : MvPolynomial (U ⊕ B) ℝ)
    {L M : ℝ} {s : ℕ} (hM : 0 ≤ M)
    (hE : ∀ b i, |E b i| ≤ L) (hp : p.totalDegree ≤ s)
    (hcoeff : ∀ α, |p.coeff α| ≤ M) :
    realPolynomialMass (aeval (polynomialTagLinearEmbedding E) p) ≤
      (((Fintype.card (U ⊕ B) : ℝ) + 1) ^ s * M) *
        (max 1 ((Fintype.card I : ℝ) * L)) ^ s := by
  have hmass : realPolynomialMass p ≤
      ((Fintype.card (U ⊕ B) : ℝ) + 1) ^ s * M :=
    monomialArray_abs_sum_le p.support id (fun _ _ _ _ h => h) s
      (fun α hα => (le_totalDegree hα).trans hp) (fun α => p.coeff α) hM
      (fun α _ => hcoeff α)
  exact (polynomialTagRestriction_mass_le E p hE hp).trans
    (mul_le_mul_of_nonneg_right hmass
      (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) s))

theorem polynomialTagRestriction_coeff_le_of_coeff_le [Fintype U] [Fintype B]
    (E : B → I → ℝ) (p : MvPolynomial (U ⊕ B) ℝ)
    {L M : ℝ} {s : ℕ} (hM : 0 ≤ M)
    (hE : ∀ b i, |E b i| ≤ L) (hp : p.totalDegree ≤ s)
    (hcoeff : ∀ α, |p.coeff α| ≤ M) (α : (U ⊕ I) →₀ ℕ) :
    |(aeval (polynomialTagLinearEmbedding E) p).coeff α| ≤
      (((Fintype.card (U ⊕ B) : ℝ) + 1) ^ s * M) *
        (max 1 ((Fintype.card I : ℝ) * L)) ^ s :=
  (realPolynomialMass_coeff_le _ α).trans
    (polynomialTagRestriction_mass_le_of_coeff_le E p hM hE hp hcoeff)

theorem polynomialSubspaceRestriction_mass_le
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (p : MvPolynomial (U ⊕ B) ℝ) {L : ℝ} {s : ℕ}
    (he : ∀ i b, |(e i : B → ℝ) b| ≤ L) (hp : p.totalDegree ≤ s) :
    realPolynomialMass (polynomialSubspaceRestriction K e p) ≤
      realPolynomialMass p * (max 1 ((Fintype.card I : ℝ) * L)) ^ s :=
  polynomialTagRestriction_mass_le _ p (fun b i => he i b) hp

theorem polynomialSubspaceRestriction_totalDegree_le
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (p : MvPolynomial (U ⊕ B) ℝ) :
    (polynomialSubspaceRestriction K e p).totalDegree ≤ p.totalDegree :=
  polynomialTagRestriction_totalDegree_le _ p

theorem polynomialSubspaceRestriction_coefficientGrid
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (p : MvPolynomial (U ⊕ B) ℝ) (q d s : ℕ)
    (he : ∀ i b, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * (e i : B → ℝ) b)
    (hp : p.totalDegree ≤ s) (hq : realPolynomialCoefficientGrid q p) :
    realPolynomialCoefficientGrid (q * d ^ s) (polynomialSubspaceRestriction K e p) :=
  polynomialTagRestriction_coefficientGrid _ p q d s (fun b i => he i b) hp hq

theorem polynomialSubspaceRestriction_coeff_le [Fintype U] [Fintype B]
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (p : MvPolynomial (U ⊕ B) ℝ) {L M : ℝ} {s : ℕ} (hM : 0 ≤ M)
    (he : ∀ i b, |(e i : B → ℝ) b| ≤ L) (hp : p.totalDegree ≤ s)
    (hcoeff : ∀ α, |p.coeff α| ≤ M) (α : (U ⊕ I) →₀ ℕ) :
    |(polynomialSubspaceRestriction K e p).coeff α| ≤
      (((Fintype.card (U ⊕ B) : ℝ) + 1) ^ s * M) *
        (max 1 ((Fintype.card I : ℝ) * L)) ^ s :=
  polynomialTagRestriction_coeff_le_of_coeff_le _ p hM (fun b i => he i b) hp hcoeff α

theorem polynomialSubspaceRestriction_coeff_div
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (p : MvPolynomial (U ⊕ B) ℝ) (q d s : ℕ) (hq : 0 < q) (hd : 0 < d)
    (he : ∀ i b, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * (e i : B → ℝ) b)
    (hp : p.totalDegree ≤ s) (hgrid : realPolynomialCoefficientGrid q p)
    (α : (U ⊕ I) →₀ ℕ) :
    ∃ z : ℤ, (polynomialSubspaceRestriction K e p).coeff α =
      (z : ℝ) / (q * d ^ s : ℕ) := by
  obtain ⟨z, hz⟩ := polynomialSubspaceRestriction_coefficientGrid K e p q d s he hp hgrid
  refine ⟨z α, (eq_div_iff ?_).mpr ?_⟩
  · exact_mod_cast (Nat.mul_pos hq (pow_pos hd s)).ne'
  · simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using (congrFun hz α).symm

theorem polynomialSubspaceRestriction_mass_le_exp
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (p : MvPolynomial (U ⊕ B) ℝ) {a v : ℝ} {s : ℕ} (hv : 0 ≤ v)
    (hdim : (Fintype.card I : ℝ) ≤ Real.exp v)
    (he : ∀ i b, |(e i : B → ℝ) b| ≤ Real.exp v)
    (hp : p.totalDegree ≤ s) (hmass : realPolynomialMass p ≤ Real.exp a) :
    realPolynomialMass (polynomialSubspaceRestriction K e p) ≤
      Real.exp (a + (s : ℝ) * (2 * v)) := by
  have hentry : max 1 ((Fintype.card I : ℝ) * Real.exp v) ≤ Real.exp (2 * v) := by
    apply max_le
    · exact Real.one_le_exp (mul_nonneg (by norm_num) hv)
    · calc
        _ ≤ Real.exp v * Real.exp v :=
          mul_le_mul_of_nonneg_right hdim (Real.exp_nonneg v)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ realPolynomialMass p * (max 1 ((Fintype.card I : ℝ) * Real.exp v)) ^ s :=
      polynomialSubspaceRestriction_mass_le K e p he hp
    _ ≤ Real.exp a * (Real.exp (2 * v)) ^ s :=
      mul_le_mul hmass (pow_le_pow_left₀
        (le_trans zero_le_one (le_max_left _ _)) hentry s)
        (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) s) (Real.exp_nonneg a)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

theorem polynomialTagRestriction_denominator_le_exp (q d s : ℕ) {v : ℝ}
    (hq : (q : ℝ) ≤ Real.exp v) (hd : (d : ℝ) ≤ Real.exp v) :
    ((q * d ^ s : ℕ) : ℝ) ≤ Real.exp (((s : ℝ) + 1) * v) := by
  simp only [Nat.cast_mul, Nat.cast_pow]
  calc
    _ ≤ Real.exp v * (Real.exp v) ^ s :=
      mul_le_mul hq (pow_le_pow_left₀ (Nat.cast_nonneg d) hd s)
        (pow_nonneg (Nat.cast_nonneg d) s) (Real.exp_nonneg v)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

theorem exists_polynomialSubspaceRestriction_denominator [Fintype B]
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (E : B → I → ℚ) (he : ∀ i b, (e i : B → ℝ) b = (E b i : ℝ))
    {H : ℕ} (hE : ∀ b i, RationalHeightLE (E b i) H)
    (q s : ℕ) (hq : 0 < q) :
    ∃ q' : ℕ, 0 < q' ∧
      q' ≤ q * H ^ ((Fintype.card B * Fintype.card I) * s) ∧ q ∣ q' ∧
      ∀ p : MvPolynomial (U ⊕ B) ℝ, p.totalDegree ≤ s →
        realPolynomialCoefficientGrid q p →
        realPolynomialCoefficientGrid q' (polynomialSubspaceRestriction K e p) := by
  classical
  let d := matrixDenominator E
  have hd : 0 < d := matrixDenominator_pos E
  have hclear : ∀ i b, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * (e i : B → ℝ) b := by
    intro i b
    refine ⟨clearedMatrix E b i, ?_⟩
    rw [he i b]
    have h := congrFun (congrFun (clearedMatrix_cast E) b) i
    change ((clearedMatrix E b i : ℤ) : ℚ) = (d : ℚ) * E b i at h
    exact_mod_cast h
  refine ⟨q * d ^ s, Nat.mul_pos hq (pow_pos hd s), ?_, dvd_mul_right q _, ?_⟩
  · apply Nat.mul_le_mul_left q
    simpa only [← pow_mul] using Nat.pow_le_pow_left (matrixDenominator_le E hE) s
  · intro p hp hgrid
    exact polynomialSubspaceRestriction_coefficientGrid K e p q d s hclear hp hgrid

end Erdos3

end

end OAI
