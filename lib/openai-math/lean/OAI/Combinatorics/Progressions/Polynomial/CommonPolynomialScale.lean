import OAI.Combinatorics.Progressions.Lattices.IntegerAxisPrincipalLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerPolynomialInitialScale (ε : ℝ) : ℕ :=
  max 1 ⌈8 * (probabilityProfileLipschitz : ℝ) / ε⌉₊

theorem integerPolynomialInitialScale_pos (ε : ℝ) : 0 < integerPolynomialInitialScale ε :=
  Nat.zero_lt_one.trans_le (le_max_left _ _)

theorem integerPolynomialInitialScale_width {ε : ℝ} (hε : 0 < ε) :
    8 * (probabilityProfileLipschitz : ℝ) ≤ ε * integerPolynomialInitialScale ε := by
  have hb : 8 * (probabilityProfileLipschitz : ℝ) / ε ≤ (integerPolynomialInitialScale ε : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈8 * (probabilityProfileLipschitz : ℝ) / ε⌉₊))
  have hm := (div_le_iff₀ hε).mp hb
  linarith

theorem exists_integer_polynomial_scale {I : Type*} [Fintype I]
    (K h : I → ℕ) (L₀ : ℕ) (γ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧ L₀ ≤ L ∧
      L ≤ max L₀ (integerPolynomialInitialScale ε) * principalSamplingGapRatio γ ^ Fintype.card I ∧
      8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L ∧
      ∀ i, L ^ h i < K i → (principalSamplingGapRatio γ * L) ^ h i ≤ K i := by
  let M := max L₀ (integerPolynomialInitialScale ε)
  have hM : 0 < M := (integerPolynomialInitialScale_pos ε).trans_le (le_max_right _ _)
  obtain ⟨L, hL, hlo, hhi, hgap⟩ := exists_integer_coefficient_scale_gap
    (fun i => (K i : ℝ)) h M (principalSamplingGapRatio γ) hM (principalSamplingGapRatio_one_le γ)
  refine ⟨L, hL, (le_max_left _ _).trans hlo, hhi, ?_, ?_⟩
  · apply (integerPolynomialInitialScale_width hε).trans
    apply mul_le_mul_of_nonneg_left _ hε.le
    exact_mod_cast (le_max_right L₀ (integerPolynomialInitialScale ε)).trans hlo
  · intro i hi
    have hb := hgap i (by exact_mod_cast hi)
    exact_mod_cast hb

noncomputable def polynomialSamplerSides {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (K : D → Option ℕ) (L : ℕ) (γ : ℝ) : SamplerTupleIndex G B h → ℕ
  | .inl _ => L
  | .inr ⟨d, _, _⟩ => match K d with
    | none => L
    | some k => integerAxisSideLength (h d) k L γ

theorem polynomialSamplerSides_pos {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (K : D → Option ℕ) {L : ℕ} (hL : 0 < L) (γ : ℝ)
    (v : SamplerTupleIndex G B h) : 0 < polynomialSamplerSides h K L γ v := by
  rcases v with g | ⟨d, b, v⟩
  · exact hL
  · simp only [polynomialSamplerSides]
    cases K d with
    | none => exact hL
    | some k => exact integerAxisSideLength_pos (hh d) hL γ

theorem polynomialSamplerSides_le {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (K : D → Option ℕ) {L : ℕ} (hL : 0 < L) (γ : ℝ)
    (v : SamplerTupleIndex G B h) : polynomialSamplerSides h K L γ v ≤ L := by
  rcases v with g | ⟨d, b, v⟩
  · exact le_rfl
  · simp only [polynomialSamplerSides]
    cases K d with
    | none => exact le_rfl
    | some k => exact integerAxisSideLength_le (hh d) hL γ

theorem polynomialSamplerSides_integer_principal {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (K : D → Option ℕ) (L : ℕ) (γ : ℝ) (d : D) (b : B d) {k : ℕ}
    (hk : K d = some k) :
    monomialScale (fun v : SamplerTupleIndex G B h => (polynomialSamplerSides h K L γ v : ℝ))
      (canonicalPrincipalExponent h d b) = (integerAxisSideLength (h d) k L γ : ℝ) ^ h d := by
  rw [monomialScale_canonicalPrincipal]
  simp only [polynomialSamplerSides, hk, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem polynomialSamplerSides_continuous_principal {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (K : D → Option ℕ) (L : ℕ) (γ : ℝ) (d : D) (b : B d) (hk : K d = none) :
    monomialScale (fun v : SamplerTupleIndex G B h => (polynomialSamplerSides h K L γ v : ℝ))
      (canonicalPrincipalExponent h d b) = (L : ℝ) ^ h d := by
  rw [monomialScale_canonicalPrincipal]
  simp only [polynomialSamplerSides, hk, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def commonPolynomialGapRatio {I : Type*} [Fintype I] (γ : I → ℝ) : ℕ :=
  max 1 (Finset.univ.sup (fun i => principalSamplingGapRatio (γ i)))

theorem commonPolynomialGapRatio_one_le {I : Type*} [Fintype I] (γ : I → ℝ) :
    1 ≤ commonPolynomialGapRatio γ := le_max_left _ _

theorem commonPolynomialGapRatio_le {I : Type*} [Fintype I] (γ : I → ℝ) (i : I) :
    principalSamplingGapRatio (γ i) ≤ commonPolynomialGapRatio γ := by
  classical
  exact (Finset.le_sup (f := fun i => principalSamplingGapRatio (γ i)) (Finset.mem_univ i)).trans
    (le_max_right _ _)

noncomputable def commonPolynomialInitialScale {J : Type*} [Fintype J]
    (L₀ : ℕ) (ε : J → ℝ) : ℕ :=
  max L₀ (max 1 (Finset.univ.sup (fun j => integerPolynomialInitialScale (ε j))))

theorem commonPolynomialInitialScale_pos {J : Type*} [Fintype J] (L₀ : ℕ) (ε : J → ℝ) :
    0 < commonPolynomialInitialScale L₀ ε :=
  Nat.zero_lt_one.trans_le ((le_max_left _ _).trans (le_max_right _ _))

theorem commonPolynomialInitialScale_le {J : Type*} [Fintype J]
    (L₀ : ℕ) (ε : J → ℝ) (j : J) :
    integerPolynomialInitialScale (ε j) ≤ commonPolynomialInitialScale L₀ ε := by
  classical
  exact (Finset.le_sup (f := fun j => integerPolynomialInitialScale (ε j)) (Finset.mem_univ j)).trans
    ((le_max_right _ _).trans (le_max_right _ _))

theorem exists_common_polynomial_scale {I J : Type*} [Fintype I] [Fintype J]
    (K h : I → ℕ) (γ : I → ℝ) (ε : J → ℝ) (hε : ∀ j, 0 < ε j) (L₀ : ℕ) :
    ∃ L : ℕ, 0 < L ∧ L₀ ≤ L ∧
      L ≤ commonPolynomialInitialScale L₀ ε * commonPolynomialGapRatio γ ^ Fintype.card I ∧
      (∀ j, 8 * (probabilityProfileLipschitz : ℝ) ≤ ε j * L) ∧
      ∀ i, L ^ h i < K i → (principalSamplingGapRatio (γ i) * L) ^ h i ≤ K i := by
  obtain ⟨L, hL, hlo, hhi, hgap⟩ := exists_integer_coefficient_scale_gap
    (fun i => (K i : ℝ)) h (commonPolynomialInitialScale L₀ ε) (commonPolynomialGapRatio γ)
    (commonPolynomialInitialScale_pos L₀ ε) (commonPolynomialGapRatio_one_le γ)
  refine ⟨L, hL, (le_max_left _ _).trans hlo, hhi, ?_, ?_⟩
  · intro j
    apply (integerPolynomialInitialScale_width (hε j)).trans
    apply mul_le_mul_of_nonneg_left _ (hε j).le
    exact_mod_cast (commonPolynomialInitialScale_le L₀ ε j).trans hlo
  · intro i hi
    have hb : (commonPolynomialGapRatio γ * L) ^ h i ≤ K i := by
      have hg := hgap i (by exact_mod_cast hi)
      exact_mod_cast hg
    exact (Nat.pow_le_pow_left (Nat.mul_le_mul_right L (commonPolynomialGapRatio_le γ i)) (h i)).trans hb

end Erdos3

end

end OAI
