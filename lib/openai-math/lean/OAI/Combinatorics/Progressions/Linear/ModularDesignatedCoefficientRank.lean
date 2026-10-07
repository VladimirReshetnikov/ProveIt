/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Polynomial.PolynomialDifferencePermanentBlocks

namespace OAI

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators Classical

theorem uniform_expect_coordinate_product {A R : Type*} [Fintype A] [DecidableEq A]
    [Fintype R] (f : A → R → ℝ) :
    (𝔼 c : A → R, ∏ b, f b (c b)) = ∏ b, 𝔼 t : R, f b t := by
  simp only [Fintype.expect_eq_sum_div_card]
  rw [← Fintype.prod_sum, Finset.prod_div_distrib]
  simp [Nat.cast_pow]

theorem uniform_selected_row_zero_probability_le {A I : Type*}
    [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (N : ℕ) [NeZero N] (row : (A → ZMod N) → I → ZMod N)
    (selected : A → I) (offset multiplier : A → ZMod N)
    (hrow : ∀ c b, row c (selected b) = offset b + c b * multiplier b) :
    (𝔼 c : A → ZMod N, if row c = 0 then (1 : ℝ) else 0) ≤
      ∏ b, (Nat.gcd (multiplier b).val N : ℝ) / N := by
  calc
    _ ≤ 𝔼 c : A → ZMod N,
        ∏ b, if c b * multiplier b + offset b = 0 then (1 : ℝ) else 0 := by
      apply Finset.expect_le_expect
      intro c _
      by_cases hc : row c = 0
      · simp only [hc, ite_true]
        have he (b : A) : c b * multiplier b + offset b = 0 := by
          have hz := congrFun hc (selected b)
          rw [hrow] at hz
          simpa only [Pi.zero_apply, add_comm] using hz
        simp only [he, ite_true, Finset.prod_const_one, le_refl]
      · simp only [hc, ite_false]
        exact Finset.prod_nonneg (fun b _ => by split_ifs <;> norm_num)
    _ = ∏ b, 𝔼 t : ZMod N,
        if t * multiplier b + offset b = 0 then (1 : ℝ) else 0 :=
      uniform_expect_coordinate_product (A := A) (R := ZMod N)
        (fun b t => if t * multiplier b + offset b = 0 then (1 : ℝ) else 0)
    _ ≤ _ := by
      apply Finset.prod_le_prod₀
      · intro b _
        exact Finset.expect_nonneg (fun t _ => by split_ifs <;> norm_num)
      · intro b _
        simpa only [mul_comm] using zmod_affine_zero_expect_le_gcd N (multiplier b) (offset b)

theorem designatedPolynomial_linearRow_zero_probability_le {A I : Type*}
    [Fintype A] [DecidableEq A] [Fintype I] [decI : DecidableEq I]
    (N : ℕ) [NeZero N] (n : ℕ) (S : A → Finset I)
    (selected : A → I) (hselected : ∀ b, selected b ∈ S b)
    (hcard : ∀ b, (S b).card = n + 1)
    (hdisjoint : Pairwise (fun b c => Disjoint (S b) (S c)))
    (Q : MvPolynomial I (ZMod N)) (u : Fin n → I → ZMod N) :
    (𝔼 c : A → ZMod N,
      if polynomialLinearRow (polynomialIterDifference n
        (Q + ∑ b, c b • ∏ i ∈ S b, X i) u) = 0 then (1 : ℝ) else 0) ≤
      ∏ b, (Nat.gcd (squarefreePermanent n ((S b).erase (selected b)) u).val N : ℝ) / N := by
  apply uniform_selected_row_zero_probability_le N _ selected
    (fun b => (polynomialIterDifference n Q u).coeff (Finsupp.single (selected b) 1))
    (fun b => squarefreePermanent n ((S b).erase (selected b)) u)
  intro c b
  have hd : decI =
      (fun i j => Classical.propDecidable (i = j)) := Subsingleton.elim _ _
  rw [hd]
  exact polynomialIterDifference_disjoint_designated_linearCoeff
    Finset.univ S c Q n b (Finset.mem_univ _) (selected b) (hselected b) (hcard b)
      (fun _ _ _ _ hbc => hdisjoint hbc) u

theorem designatedPolynomial_expected_linearRow_zero_le {A I : Type*}
    [Fintype A] [DecidableEq A] [Fintype I] [decI : DecidableEq I]
    {p a n : ℕ} [NeZero p] (hp : p.Prime) (ha : 0 < a)
    (S : A → Finset I) (selected : A → I)
    (hselected : ∀ b, selected b ∈ S b) (hcard : ∀ b, (S b).card = n + 1)
    (hdisjoint : Pairwise (fun b c => Disjoint (S b) (S c)))
    (Q : MvPolynomial I (ZMod (p ^ a))) :
    (𝔼 c : A → ZMod (p ^ a), 𝔼 u : Fin n → I → ZMod (p ^ a),
      if polynomialLinearRow (polynomialIterDifference n
        (Q + ∑ b, c b • ∏ i ∈ S b, X i) u) = 0 then (1 : ℝ) else 0) ≤
      (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n)) ^ Fintype.card A := by
  have hc (b : A) : Fintype.card ((S b).erase (selected b)) = n := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem (hselected b), hcard]
    omega
  let e (b : A) : Fin n ≃ (S b).erase (selected b) := (Fintype.equivFinOfCardEq (hc b)).symm
  let v (b : A) (j : Fin n) : I := (e b j).val
  have hv : ∀ b ∈ (Finset.univ : Finset A), Function.Injective (v b) := by
    intro b _ i j hij
    exact (e b).injective (Subtype.ext hij)
  have hsep : ((Finset.univ : Finset A) : Set A).Pairwise (fun b c =>
      Disjoint (Finset.univ.image (v b)) (Finset.univ.image (v c))) := by
    intro b _ c _ hbc
    apply Finset.disjoint_left.mpr
    intro i hib hic
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hib
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hic
    have hj : v b j ∈ S b := (Finset.mem_erase.mp (e b j).property).2
    have hk' : v b j ∈ S c := hk ▸ (Finset.mem_erase.mp (e c k).property).2
    exact Finset.disjoint_left.mp (hdisjoint hbc) hj hk'
  have hperm (b : A) (u : Fin n → I → ZMod (p ^ a)) :
      squarefreePermanent n ((S b).erase (selected b)) u =
        Matrix.permanent (fun i j => u i (v b j)) :=
    squarefreePermanent_eq_matrix_permanent n _ (e b) u
  rw [Finset.expect_comm]
  calc
    _ ≤ 𝔼 u : Fin n → I → ZMod (p ^ a),
        ∏ b, (Nat.gcd (squarefreePermanent n ((S b).erase (selected b)) u).val
          (p ^ a) : ℝ) / (p ^ a : ℕ) := by
      apply Finset.expect_le_expect
      intro u _
      exact designatedPolynomial_linearRow_zero_probability_le (p ^ a) n S selected
        hselected hcard hdisjoint Q u
    _ ≤ _ := by
      simp_rw [hperm]
      simpa only [Finset.card_univ] using
        disjoint_permanent_gcd_mean_bound_curried_all hp ha Finset.univ v hv hsep

theorem uniform_expect_unit_scaled_coefficients {A R : Type*}
    [Fintype A] [DecidableEq A] [Fintype R] [Monoid R]
    (unit : A → Rˣ) (F : (A → R) → ℝ) :
    (𝔼 c : A → R, F (fun b => (unit b : R) * c b)) = 𝔼 c : A → R, F c := by
  apply Fintype.expect_equiv (Equiv.piCongrRight (fun b => Units.mulLeft (unit b)))
  intro c
  rfl

theorem designatedPolynomial_expected_unit_linearRow_zero_le {A I : Type*}
    [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    {p a n : ℕ} [NeZero p] (hp : p.Prime) (ha : 0 < a)
    (S : A → Finset I) (selected : A → I)
    (hselected : ∀ b, selected b ∈ S b) (hcard : ∀ b, (S b).card = n + 1)
    (hdisjoint : Pairwise (fun b c => Disjoint (S b) (S c)))
    (Q : MvPolynomial I (ZMod (p ^ a))) (unit : A → (ZMod (p ^ a))ˣ) :
    (𝔼 c : A → ZMod (p ^ a), 𝔼 u : Fin n → I → ZMod (p ^ a),
      if polynomialLinearRow (polynomialIterDifference n
        (Q + ∑ b, ((unit b : ZMod (p ^ a)) * c b) • ∏ i ∈ S b, X i) u) = 0
          then (1 : ℝ) else 0) ≤
      (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n)) ^ Fintype.card A := by
  have he := uniform_expect_unit_scaled_coefficients unit (fun c =>
    𝔼 u : Fin n → I → ZMod (p ^ a),
      if polynomialLinearRow (polynomialIterDifference n
        (Q + ∑ b, c b • ∏ i ∈ S b, X i) u) = 0 then (1 : ℝ) else 0)
  rw [he]
  exact designatedPolynomial_expected_linearRow_zero_le hp ha S selected
    hselected hcard hdisjoint Q

theorem designatedPolynomial_expected_rank_failure_le {A I : Type*}
    [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    {p a n : ℕ} [NeZero p] (hp : p.Prime) (ha : 0 < a)
    (S : A → Finset I) (hcard : ∀ b, (S b).card = n + 1)
    (hdisjoint : Pairwise (fun b c => Disjoint (S b) (S c)))
    (Q : MvPolynomial I (ZMod (p ^ a))) (unit : A → (ZMod (p ^ a))ˣ) :
    (𝔼 c : A → ZMod (p ^ a), 𝔼 u : Fin n → I → ZMod (p ^ a),
      if polynomialLinearRow (polynomialIterDifference n
        (Q + ∑ b, ((unit b : ZMod (p ^ a)) * c b) • ∏ i ∈ S b, X i) u) = 0
          then (1 : ℝ) else 0) ≤
      (((n + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(a : ℝ) / (2 : ℝ) ^ n)) ^ Fintype.card A := by
  have hnonempty (b : A) : (S b).Nonempty :=
    Finset.card_pos.mp (by rw [hcard]; omega)
  choose selected hselected using hnonempty
  exact designatedPolynomial_expected_unit_linearRow_zero_le hp ha S selected
    hselected hcard hdisjoint Q unit

end Erdos3

end

end OAI
