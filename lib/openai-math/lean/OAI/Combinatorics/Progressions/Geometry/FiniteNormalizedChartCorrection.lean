/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.FiniteEnumerationFilter
import OAI.Combinatorics.Progressions.Linear.FiniteRankTriangularFinset
import OAI.Combinatorics.Progressions.Polynomial.FiniteSupportedPolynomialSubstitution
import OAI.Combinatorics.Progressions.Polynomial.MajorWeightedDegreeTools

namespace OAI

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators Classical

variable {U B : Type*}

noncomputable def normalizedChartTagWeight : U ⊕ B → ℕ :=
  Sum.elim (fun _ => 0) (fun _ => 1)

private theorem normalizedChart_spatial_support (P : MvPolynomial U ℝ) :
    rename (Sum.inl : U → U ⊕ B) P ∈ weightedSupportLE normalizedChartTagWeight 0 := by
  rw [rename_eq_aeval]
  apply weightedSupportLE_aeval (fun _ : U => 0) normalizedChartTagWeight
  · intro i
    exact weightedSupportLE_X _ (Sum.inl i)
  · intro α _
    simp [Finsupp.weight_apply]

theorem normalizedRealPolynomialChart_tag_support
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (i : U ⊕ B) :
    normalizedRealPolynomialChart H A i ∈
      weightedSupportLE normalizedChartTagWeight (normalizedChartTagWeight i) := by
  cases i with
  | inl i =>
    change C ((H i)⁻¹) * X (Sum.inl i) ∈ weightedSupportLE
      (normalizedChartTagWeight (U := U) (B := B)) 0
    exact weightedSupportLE_mul
      (w := normalizedChartTagWeight (U := U) (B := B)) (d := 0) (e := 0)
      (weightedSupportLE_C _ 0 ((H i)⁻¹)) (weightedSupportLE_X _ (Sum.inl i))
  | inr i =>
    change X (Sum.inr i) - rename Sum.inl (A i) ∈ weightedSupportLE
      (normalizedChartTagWeight (U := U) (B := B)) 1
    exact (weightedSupportLE (normalizedChartTagWeight (U := U) (B := B)) 1).sub_mem
      (weightedSupportLE_X _ (Sum.inr i))
      (weightedSupportLE_mono (Nat.zero_le 1) (normalizedChart_spatial_support (A i)))

theorem normalizedRealPolynomialChart_tag_coordinate_difference
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (i : U ⊕ B) :
    normalizedRealPolynomialChart H A i -
      normalizedRealPolynomialChart H (fun _ => 0) i ∈
        weightedSupportLT normalizedChartTagWeight (normalizedChartTagWeight i) := by
  cases i with
  | inl i =>
    simp only [normalizedRealPolynomialChart_inl, sub_self]
    exact Submodule.zero_mem _
  | inr i =>
    change (X (Sum.inr i) - rename Sum.inl (A i)) -
      (X (Sum.inr i) - rename Sum.inl (0 : MvPolynomial U ℝ)) ∈
        weightedSupportLT (normalizedChartTagWeight (U := U) (B := B)) 1
    rw [map_zero, sub_zero, sub_sub_cancel_left]
    exact (weightedSupportLT (normalizedChartTagWeight (U := U) (B := B)) 1).neg_mem
      (weightedSupportLE_lt_succ (normalizedChart_spatial_support (A i)))

private theorem normalizedChart_hom_tag_support
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (i : U ⊕ B) :
    (aeval (R := ℝ) (normalizedRealPolynomialChart H A)) (X i) ∈
      weightedSupportLE normalizedChartTagWeight (normalizedChartTagWeight i) := by
  rw [aeval_X]
  exact normalizedRealPolynomialChart_tag_support H A i

private theorem normalizedChart_hom_tag_difference
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (i : U ⊕ B) :
    (aeval (R := ℝ) (normalizedRealPolynomialChart H A)) (X i) -
      (aeval (R := ℝ) (normalizedRealPolynomialChart H (fun _ => 0))) (X i) ∈
        weightedSupportLT normalizedChartTagWeight (normalizedChartTagWeight i) := by
  rw [aeval_X, aeval_X]
  exact normalizedRealPolynomialChart_tag_coordinate_difference H A i

theorem normalizedRealPolynomialChart_tag_difference
    (H : U → ℝ) (A : B → MvPolynomial U ℝ) (α : (U ⊕ B) →₀ ℕ) :
    aeval (R := ℝ) (normalizedRealPolynomialChart H A) (monomial α 1) -
      aeval (R := ℝ) (normalizedRealPolynomialChart H (fun _ => 0)) (monomial α 1) ∈
        weightedSupportLT normalizedChartTagWeight (Finsupp.weight normalizedChartTagWeight α) :=
  weightedComparison_monomial_one
    (normalizedChartTagWeight (U := U) (B := B)) normalizedChartTagWeight
    (aeval (R := ℝ) (normalizedRealPolynomialChart H A))
    (aeval (R := ℝ) (normalizedRealPolynomialChart H (fun _ => 0)))
    (normalizedChart_hom_tag_support H A)
    (normalizedChart_hom_tag_support H (fun _ => 0))
    (normalizedChart_hom_tag_difference H A) α

theorem aeval_coordinate_scaling_monomial {I : Type*}
    (c : I → ℝ) (α : I →₀ ℕ) :
    aeval (R := ℝ) (fun i => C (c i) * X i) (monomial α 1) =
      monomial α (α.prod (fun i n => c i ^ n)) := by
  classical
  rw [aeval_monomial]
  simp only [map_one, one_mul, Finsupp.prod,
    mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, monomial_eq]

noncomputable def normalizedChartDiagonal (H : U → ℝ) (α : (U ⊕ B) →₀ ℕ) : ℝ :=
  α.prod (fun i n => (Sum.elim (fun u => (H u)⁻¹) (fun _ : B => 1) i) ^ n)

theorem normalizedChart_zero_monomial (H : U → ℝ) (α : (U ⊕ B) →₀ ℕ) :
    aeval (R := ℝ) (normalizedRealPolynomialChart H (fun _ : B => 0)) (monomial α 1) =
      monomial α (normalizedChartDiagonal H α) := by
  have h : normalizedRealPolynomialChart H (fun _ : B => 0) =
      fun i => C (Sum.elim (fun u => (H u)⁻¹) (fun _ : B => 1) i) * X i := by
    funext i
    cases i <;> simp [normalizedRealPolynomialChart]
  rw [h]
  exact aeval_coordinate_scaling_monomial _ α

theorem normalizedChart_coeff_of_tag_le (H : U → ℝ) (A : B → MvPolynomial U ℝ)
    (α β : (U ⊕ B) →₀ ℕ)
    (h : Finsupp.weight normalizedChartTagWeight α ≤ Finsupp.weight normalizedChartTagWeight β) :
    (aeval (R := ℝ) (normalizedRealPolynomialChart H A) (monomial α 1)).coeff β =
      if α = β then normalizedChartDiagonal H α else 0 := by
  classical
  have hd := normalizedRealPolynomialChart_tag_difference H A α
  have hz : (aeval (R := ℝ) (normalizedRealPolynomialChart H A) (monomial α 1) -
      aeval (R := ℝ) (normalizedRealPolynomialChart H (fun _ => 0)) (monomial α 1)).coeff β = 0 := by
    by_contra hn
    exact (not_lt_of_ge h) (hd (mem_support_iff.mpr hn))
  rw [coeff_sub, normalizedChart_zero_monomial, coeff_monomial] at hz
  exact sub_eq_zero.mp hz

theorem normalizedChartDiagonal_pos_le_one (H : U → ℝ) (hH : ∀ i, 1 ≤ H i)
    (α : (U ⊕ B) →₀ ℕ) :
    0 < normalizedChartDiagonal H α ∧ normalizedChartDiagonal H α ≤ 1 := by
  classical
  have hscale (i : U ⊕ B) :
      0 < Sum.elim (fun u => (H u)⁻¹) (fun _ : B => (1 : ℝ)) i ∧
        Sum.elim (fun u => (H u)⁻¹) (fun _ : B => (1 : ℝ)) i ≤ 1 := by
    cases i with
    | inl i => exact ⟨inv_pos.mpr (lt_of_lt_of_le zero_lt_one (hH i)),
        inv_le_one_of_one_le₀ (hH i)⟩
    | inr i => exact ⟨zero_lt_one, le_rfl⟩
  unfold normalizedChartDiagonal Finsupp.prod
  refine ⟨Finset.prod_pos (fun i _ => pow_pos (hscale i).1 _), ?_⟩
  exact Finset.prod_le_one₀ (fun i _ => pow_nonneg (hscale i).1.le _)
    (fun i _ => pow_le_one₀ (hscale i).1.le (hscale i).2)

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {U V : Type*}

def normalizedChartCorrectionSolutions
    (H : U → ℝ) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (P : MvPolynomial (U ⊕ V) ℝ) (B : ℝ) (q : ℕ) :
    Set (MvPolynomial (U ⊕ V) ℝ × MvPolynomial (U ⊕ V) ℚ) :=
  {sr | sr.1.support ⊆ S ∧ sr.2.support ⊆ S ∧
    (∀ α, |sr.1.coeff α| ≤ B) ∧
    (∀ α, ∃ z : ℤ, sr.2.coeff α = (z : ℚ) / q) ∧
    P = aeval (R := ℝ) (normalizedRealPolynomialChart H A) sr.1 +
      MvPolynomial.map (Rat.castHom ℝ) sr.2}

noncomputable def normalizedChartCoefficientMatrix
    (H : U → ℝ) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) : Matrix S S ℝ :=
  fun β α =>
    (aeval (R := ℝ) (normalizedRealPolynomialChart H A) (monomial α.val 1)).coeff β.val

theorem normalizedChartCoefficientMatrix_triangular
    (H : U → ℝ) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (α β : S)
    (h : Finsupp.weight normalizedChartTagWeight β.val ≤
      Finsupp.weight normalizedChartTagWeight α.val) (hne : β ≠ α) :
    normalizedChartCoefficientMatrix H A S α β = 0 := by
  classical
  have hval : β.val ≠ α.val := fun he => hne (Subtype.ext he)
  simp only [normalizedChartCoefficientMatrix, normalizedChart_coeff_of_tag_le H A β.val α.val h,
    hval, ite_false]

theorem normalizedChartCoefficientMatrix_diagonal
    (H : U → ℝ) (hH : ∀ i, 1 ≤ H i) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (α : S) :
    normalizedChartCoefficientMatrix H A S α α ≠ 0 ∧
      |normalizedChartCoefficientMatrix H A S α α| ≤ 1 := by
  classical
  rw [normalizedChartCoefficientMatrix,
    normalizedChart_coeff_of_tag_le H A α.val α.val le_rfl]
  simp only [ite_true]
  obtain ⟨hpos, hle⟩ := normalizedChartDiagonal_pos_le_one H hH α.val
  exact ⟨hpos.ne', (abs_of_pos hpos).trans_le hle⟩

theorem normalizedChartCoefficientMatrix_coeff_aeval
    (H : U → ℝ) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (slow : MvPolynomial (U ⊕ V) ℝ)
    (hsupport : slow.support ⊆ S) (β : S) :
    (aeval (R := ℝ) (normalizedRealPolynomialChart H A) slow).coeff β.val =
      ∑ α : S, normalizedChartCoefficientMatrix H A S β α * slow.coeff α.val := by
  classical
  unfold normalizedChartCoefficientMatrix
  conv_lhs => rw [← polynomialOfFiniteCoefficientVector_reconstruct S slow hsupport]
  rw [polynomialOfFiniteCoefficientVector, map_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro α _
  simp only [aeval_monomial, MvPolynomial.algebraMap_eq, map_one, one_mul, coeff_C_mul]
  exact mul_comm _ _

private theorem normalizedChartCorrectionSolutions_coefficients
    (H : U → ℝ) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (P : MvPolynomial (U ⊕ V) ℝ) (B : ℝ) (q : ℕ)
    (sr : MvPolynomial (U ⊕ V) ℝ × MvPolynomial (U ⊕ V) ℚ)
    (hsr : sr ∈ normalizedChartCorrectionSolutions H A S P B q) :
    ((fun α : S => sr.1.coeff α.val), (fun α : S => sr.2.coeff α.val)) ∈
      finiteRankCorrectionSolutions (normalizedChartCoefficientMatrix H A S)
        (fun α : S => P.coeff α.val) B q := by
  classical
  rcases hsr with ⟨hslow, _, hbound, hgrid, hidentity⟩
  refine ⟨fun α => hbound α.val, fun α => hgrid α.val, ?_⟩
  intro β
  have heq := congrArg (fun polynomial : MvPolynomial (U ⊕ V) ℝ => polynomial.coeff β.val) hidentity
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_map,
    normalizedChartCoefficientMatrix_coeff_aeval H A S sr.1 hslow β] at heq
  exact heq

theorem exists_finite_normalized_chart_corrections
    (H : U → ℝ) (hH : ∀ i, 1 ≤ H i) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (P : MvPolynomial (U ⊕ V) ℝ)
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q) :
    ∃ m : ℕ, m ≤ (2 * ⌈(q : ℝ) * B⌉₊ + 3) ^ S.card ∧
      ∃ candidate : Fin m → (MvPolynomial (U ⊕ V) ℝ × MvPolynomial (U ⊕ V) ℚ),
        (∀ j, candidate j ∈ normalizedChartCorrectionSolutions H A S P B q) ∧
        ∀ sr, sr ∈ normalizedChartCorrectionSolutions H A S P B q →
          ∃ j, candidate j = sr := by
  classical
  let rank := fun α : S => Finsupp.weight normalizedChartTagWeight α.val
  obtain ⟨n, hn, vectors, _, hcover⟩ :=
    exists_finite_rank_triangular_correction_enumeration q hq B hB rank
      (normalizedChartCoefficientMatrix H A S) (fun α : S => P.coeff α.val)
      (normalizedChartCoefficientMatrix_triangular H A S)
      (fun α => (normalizedChartCoefficientMatrix_diagonal H hH A S α).1)
      (fun α => (normalizedChartCoefficientMatrix_diagonal H hH A S α).2)
  let polynomials := fun j : Fin n =>
    (polynomialOfFiniteCoefficientVector S (vectors j).1,
      polynomialOfFiniteCoefficientVector S (vectors j).2)
  have hpolynomials (sr) (hsr : sr ∈ normalizedChartCorrectionSolutions H A S P B q) :
      ∃ j, polynomials j = sr := by
    obtain ⟨j, hj⟩ := hcover _
      (normalizedChartCorrectionSolutions_coefficients H A S P B q sr hsr)
    refine ⟨j, ?_⟩
    dsimp only [polynomials]
    rw [hj]
    exact Prod.ext (polynomialOfFiniteCoefficientVector_reconstruct S sr.1 hsr.1)
      (polynomialOfFiniteCoefficientVector_reconstruct S sr.2 hsr.2.1)
  obtain ⟨m, hm, candidate, hvalid, _, hcomplete⟩ :=
    exists_filtered_finite_enumeration polynomials
      (fun sr => sr ∈ normalizedChartCorrectionSolutions H A S P B q)
  refine ⟨m, ?_, candidate, hvalid, ?_⟩
  · exact hm.trans (by simpa only [Fintype.card_coe] using hn)
  · intro sr hsr
    exact hcomplete sr hsr (hpolynomials sr hsr)

end Erdos3

end

end OAI
