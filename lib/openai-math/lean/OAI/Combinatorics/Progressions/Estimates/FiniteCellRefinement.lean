import OAI.Combinatorics.Progressions.Estimates.LocalWeightCaps

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def matchedCellSpace (L S : Finset G) : Finset (G × (G × G)) := L ×ˢ (S ×ˢ S)

noncomputable def matchedFirstCell (C : Finset G) (f : G → ℝ) (z : G × (G × G)) : ℝ :=
  cellAverage C f z.1

noncomputable def matchedSecondCell (C : Finset G) (f : G → ℝ) (z : G × (G × G)) : ℝ :=
  cellAverage C f (-z.1 + z.2.1 + z.2.2)

omit [AddCommGroup G] [Fintype G] [DecidableEq G] in
theorem matchedCellSpace_nonempty {L S : Finset G} (hL : L.Nonempty) (hS : S.Nonempty) :
    (matchedCellSpace L S).Nonempty := hL.product (hS.product hS)

omit [Fintype G] [DecidableEq G] in
theorem expect_matchedFirstCell (L S C : Finset G) (hS : S.Nonempty) (f : G → ℝ) :
    (𝔼 z ∈ matchedCellSpace L S, matchedFirstCell C f z) = 𝔼 r ∈ L, cellAverage C f r := by
  simp only [matchedCellSpace, Finset.expect_product, matchedFirstCell, Finset.expect_const hS]

omit [Fintype G] [DecidableEq G] in
theorem expect_matchedFirstCell_sq (L S C : Finset G) (hS : S.Nonempty) (f : G → ℝ) :
    (𝔼 z ∈ matchedCellSpace L S, matchedFirstCell C f z ^ 2) =
      𝔼 r ∈ L, cellAverage C f r ^ 2 := by
  simp only [matchedCellSpace, Finset.expect_product, matchedFirstCell, Finset.expect_const hS]

theorem mean_matchedFirstCell_le (L S C : Finset G) (hS : S.Nonempty) (hC : C.Nonempty)
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ L → f x = 0) :
    (𝔼 z ∈ matchedCellSpace L S, matchedFirstCell C f z) ≤ 𝔼 r ∈ L, f r := by
  rw [expect_matchedFirstCell L S C hS]
  exact expect_cellAverage_comp_le L C hC f hf hsupport id Function.injective_id

theorem mean_matchedSecondCell_le (L S C : Finset G) (hS : S.Nonempty) (hC : C.Nonempty)
    (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ L → f x = 0) :
    (𝔼 z ∈ matchedCellSpace L S, matchedSecondCell C f z) ≤ 𝔼 r ∈ L, f r := by
  have hpoint (s t : G) : (𝔼 r ∈ L, cellAverage C f (-r + s + t)) ≤ 𝔼 r ∈ L, f r :=
    expect_cellAverage_comp_le L C hC f hf hsupport (fun r => -r + s + t)
      (fun _ _ h => neg_injective (add_right_cancel (add_right_cancel h)))
  have h := Finset.expect_le_expect (fun s (_ : s ∈ S) =>
    Finset.expect_le_expect (fun t (_ : t ∈ S) => hpoint s t))
  simp only [Finset.expect_const hS] at h
  simp only [matchedCellSpace, Finset.expect_product, matchedSecondCell]
  have horder : (𝔼 r ∈ L, 𝔼 s ∈ S, 𝔼 t ∈ S, cellAverage C f (-r + s + t)) =
      𝔼 s ∈ S, 𝔼 t ∈ S, 𝔼 r ∈ L, cellAverage C f (-r + s + t) := by
    rw [Finset.expect_comm L S]
    apply Finset.expect_congr rfl
    intro s _
    exact Finset.expect_comm L S _
  rwa [horder]

theorem matched_cell_potential_le (L S C : Finset G)
    (hL : L.Nonempty) (hS : S.Nonempty) (hC : C.Nonempty)
    (f g : G → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ L → f x = 0) (hgsupport : ∀ x, x ∉ L → g x = 0) :
    (𝔼 z ∈ matchedCellSpace L S,
      (matchedFirstCell C f z * matchedSecondCell C g z) ^ (1 / 4 : ℝ)) ≤
      ((𝔼 r ∈ L, f r) * (𝔼 r ∈ L, g r)) ^ (1 / 4 : ℝ) := by
  exact expect_quarter_product_le (matchedCellSpace L S) (matchedCellSpace_nonempty hL hS)
    (matchedFirstCell C f) (matchedSecondCell C g)
    (fun z => cellAverage_nonneg C f hf z.1)
    (fun z => cellAverage_nonneg C g hg (-z.1 + z.2.1 + z.2.2))
    (mean_matchedFirstCell_le L S C hS hC f hf hfsupport)
    (mean_matchedSecondCell_le L S C hS hC g hg hgsupport)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem expect_outside_reflected_le (L : Finset G) (hsymm : -L = L) (q : G)
    {eta : ℝ} (hTV : (∑ x, |realUniformMass L (x - q) - realUniformMass L x|) ≤ eta) :
    (𝔼 r ∈ L, if -r + q ∈ L then (0 : ℝ) else 1) ≤ eta := by
  let out : G → ℝ := fun x => if x ∈ L then 0 else 1
  have hbound (x : G) : |out x| ≤ 1 := by
    dsimp [out]
    split_ifs <;> norm_num
  have hzero : (𝔼 x ∈ L, out x) = 0 := by
    calc
      _ = 𝔼 _x ∈ L, (0 : ℝ) := Finset.expect_congr rfl (fun x hx => by simp [out, hx])
      _ = 0 := by simp
  have h := abs_expect_add_sub_le L out q hbound
  rw [hzero, sub_zero, one_mul] at h
  change (𝔼 r ∈ L, out (-r + q)) ≤ eta
  rw [expect_neg_add_eq L hsymm out q]
  exact (le_abs_self _).trans (h.trans hTV)

theorem abs_reflected_restriction_le (L : Finset G) (hsymm : -L = L)
    (F : G → G → ℝ) (q : G) {M eta : ℝ} (hM : 0 ≤ M) (hF : ∀ x y, |F x y| ≤ M)
    (hTV : (∑ x, |realUniformMass L (x - q) - realUniformMass L x|) ≤ eta) :
    |(𝔼 r ∈ L, F r (-r + q)) -
      𝔼 r ∈ L, if -r + q ∈ L then F r (-r + q) else 0| ≤ M * eta := by
  rw [← Finset.expect_sub_distrib]
  have hnorm := RCLike.norm_expect_le (K := ℝ) (s := L)
    (f := fun r => F r (-r + q) - if -r + q ∈ L then F r (-r + q) else 0)
  calc
    _ ≤ 𝔼 r ∈ L, |F r (-r + q) - if -r + q ∈ L then F r (-r + q) else 0| := by
      simpa only [Real.norm_eq_abs] using hnorm
    _ ≤ 𝔼 r ∈ L, M * (if -r + q ∈ L then (0 : ℝ) else 1) := by
      apply Finset.expect_le_expect
      intro r _
      by_cases hr : -r + q ∈ L
      · simp only [hr, ite_true, sub_self, abs_zero, mul_zero, le_refl]
      · simpa only [hr, ite_false, sub_zero, mul_one] using hF r (-r + q)
    _ = M * (𝔼 r ∈ L, if -r + q ∈ L then (0 : ℝ) else 1) := (Finset.mul_expect _ _ _).symm
    _ ≤ M * eta := mul_le_mul_of_nonneg_left (expect_outside_reflected_le L hsymm q hTV) hM

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem bilinearIntegral_restrict (A B : Finset G) (a f g : G → ℝ) :
    bilinearIntegral A B a (Peeling.slice A f) (Peeling.slice B g) =
      bilinearIntegral A B a f g := by
  apply Finset.expect_congr rfl
  intro x hx
  apply Finset.expect_congr rfl
  intro y hy
  simp only [Peeling.slice, hx, hy, ite_true]

theorem bilinearIntegral_translate (A B : Finset G) (a f g : G → ℝ) (x₀ y₀ : G) :
    bilinearIntegral (A.image (fun x => x₀ + x)) (B.image (fun y => y₀ + y)) a f g =
      bilinearIntegral A B (fun z => a (x₀ + y₀ + z)) (fun x => f (x₀ + x))
        (fun y => g (y₀ + y)) := by
  unfold bilinearIntegral
  rw [Finset.expect_image (fun _ _ _ _ h => add_left_cancel h)]
  apply Finset.expect_congr rfl
  intro x _
  rw [Finset.expect_image (fun _ _ _ _ h => add_left_cancel h)]
  apply Finset.expect_congr rfl
  intro y _
  have heq : x₀ + x + (y₀ + y) = x₀ + y₀ + (x + y) := by abel
  rw [heq]

theorem replacementIntegral_eq_restricted_cells (D Q C : Finset G) (a f g : G → ℝ) :
    replacementIntegral D Q C a f g =
      𝔼 z ∈ Q, bilinearIntegral D (C.image (fun t => z + t)) a
        (Peeling.slice D f) (Peeling.slice (C.image (fun t => z + t)) g) := by
  rw [replacementIntegral_eq_cells]
  apply Finset.expect_congr rfl
  intro z _
  exact (bilinearIntegral_restrict D (C.image (fun t => z + t)) a f g).symm

theorem replacementIntegral_common_shape (Q C : Finset G) (a f g : G → ℝ) (x₀ : G) :
    replacementIntegral (C.image (fun t => x₀ + t)) Q C a f g =
      𝔼 y₀ ∈ Q, bilinearIntegral C C (fun z => a (x₀ + y₀ + z))
        (fun x => f (x₀ + x)) (fun y => g (y₀ + y)) := by
  rw [replacementIntegral_eq_cells]
  apply Finset.expect_congr rfl
  intro y₀ _
  exact bilinearIntegral_translate C C a f g x₀ y₀

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

noncomputable def matchedPairAverage (L S : Finset G) (F : G → G → ℝ) : ℝ :=
  𝔼 r ∈ L, 𝔼 s ∈ S, 𝔼 t ∈ S, F r (-r + s + t)

theorem matchedPairAverage_eq_space (L S : Finset G) (F : G → G → ℝ) :
    matchedPairAverage L S F =
      𝔼 z ∈ matchedCellSpace L S, F z.1 (-z.1 + z.2.1 + z.2.2) := by
  simp only [matchedPairAverage, matchedCellSpace, Finset.expect_product]

theorem expect_matchedPairAverage {ι : Type*} (I : Finset ι) (L S : Finset G)
    (F : ι → G → G → ℝ) :
    (𝔼 i ∈ I, matchedPairAverage L S (F i)) =
      matchedPairAverage L S (fun x y => 𝔼 i ∈ I, F i x y) := by
  unfold matchedPairAverage
  rw [Finset.expect_comm I L]
  apply Finset.expect_congr rfl
  intro r _
  rw [Finset.expect_comm I S]
  apply Finset.expect_congr rfl
  intro s _
  exact Finset.expect_comm I S _

theorem matchedPairAverage_const (L S : Finset G) (hL : L.Nonempty) (hS : S.Nonempty) (b : ℝ) :
    matchedPairAverage L S (fun _ _ => b) = b := by
  simp only [matchedPairAverage, Finset.expect_const hL, Finset.expect_const hS]

theorem abs_matchedPairAverage_sub_le (L S : Finset G) (hL : L.Nonempty) (hS : S.Nonempty)
    (F H : G → G → ℝ) {epsilon : ℝ}
    (hFH : ∀ x y, |F x y - H x y| ≤ epsilon) :
    |matchedPairAverage L S F - matchedPairAverage L S H| ≤ epsilon := by
  unfold matchedPairAverage
  apply abs_expect_sub_expect_le L hL
  intro r _
  apply abs_expect_sub_expect_le S hS
  intro s _
  exact abs_expect_sub_expect_le S hS _ _ (fun t _ => hFH r (-r + s + t))

variable [Fintype G] [DecidableEq G]

theorem abs_matchedPairAverage_shift_sub_le
    (L S : Finset G) (hL : L.Nonempty) (hS : S.Nonempty) (F : G → G → ℝ)
    (u v : G) {M etaL etaS : ℝ} (hM : 0 ≤ M) (hF : ∀ x y, |F x y| ≤ M)
    (hLshift : (∑ x, |realUniformMass L (x - u) - realUniformMass L x|) ≤ etaL)
    (hSshift : (∑ x, |realUniformMass S (x - (u + v)) - realUniformMass S x|) ≤ etaS) :
    |matchedPairAverage L S (fun x y => F (x + u) (y + v)) -
      matchedPairAverage L S F| ≤ M * (etaL + etaS) := by
  have horder (H : G → G → ℝ) : matchedPairAverage L S H =
      𝔼 t ∈ S, 𝔼 r ∈ L, 𝔼 s ∈ S, H r (-r + s + t) := by
    unfold matchedPairAverage
    have hin (r : G) : (𝔼 s ∈ S, 𝔼 t ∈ S, H r (-r + s + t)) =
        𝔼 t ∈ S, 𝔼 s ∈ S, H r (-r + s + t) := Finset.expect_comm S S _
    simp_rw [hin]
    exact Finset.expect_comm L S _
  rw [horder, horder]
  apply abs_expect_sub_expect_le S hS
  intro t _
  have h := abs_expect_pair_add_sub_le L S hL hS (fun r s => F r (-r + s + t))
    u (u + v) hM (fun r s => hF r (-r + s + t)) hLshift hSshift
  have heq (r s : G) : -(r + u) + (s + (u + v)) + t = (-r + s + t) + v := by abel
  simpa only [heq] using h

end Erdos3.CellRefinement

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
theorem cellAverage_div (C : Finset G) (f : G → ℝ) (u : ℝ) (x : G) :
    cellAverage C (fun y => f y / u) x = cellAverage C f x / u :=
  (Finset.expect_div C (fun c => f (x + c)) u).symm

theorem matchedSecondCell_second_moment_ge
    (L S C : Finset G) (hL : -L = L) (hS : S.Nonempty) (hC : C.Nonempty)
    (f : G → ℝ) {M eta : ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M)
    (hTV : ∀ s ∈ S, ∀ t ∈ S,
      (∑ x, |realUniformMass L (x - (s + t)) - realUniformMass L x|) ≤ eta) :
    (𝔼 x ∈ L, cellAverage C f x ^ 2) - M ^ 2 * eta ≤
      𝔼 z ∈ matchedCellSpace L S, matchedSecondCell C f z ^ 2 := by
  have hbound (x : G) : |cellAverage C f x ^ 2| ≤ M ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (cellAverage_nonneg C f (fun y => (hf y).1) x)
      (cellAverage_le hC f (fun y => (hf y).2) x) 2
  have hshift (s : G) (hs : s ∈ S) (t : G) (ht : t ∈ S) :
      (𝔼 x ∈ L, cellAverage C f x ^ 2) - M ^ 2 * eta ≤
        𝔼 x ∈ L, cellAverage C f (-x + s + t) ^ 2 := by
    simpa only [add_assoc] using reflected_average_sub_le L hL
      (fun x => cellAverage C f x ^ 2) (s + t) (sq_nonneg M) hbound (hTV s hs t ht)
  have h := Finset.expect_le_expect (fun s (hs : s ∈ S) =>
    Finset.expect_le_expect (fun t (ht : t ∈ S) => hshift s hs t ht))
  simp only [Finset.expect_const hS] at h
  simp only [matchedCellSpace, Finset.expect_product, matchedSecondCell]
  have horder : (𝔼 x ∈ L, 𝔼 s ∈ S, 𝔼 t ∈ S, cellAverage C f (-x + s + t) ^ 2) =
      𝔼 s ∈ S, 𝔼 t ∈ S, 𝔼 x ∈ L, cellAverage C f (-x + s + t) ^ 2 := by
    rw [Finset.expect_comm L S]
    apply Finset.expect_congr rfl
    intro s _
    exact Finset.expect_comm L S _
  rwa [horder]

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

noncomputable def matchedIndependentAverage (L S C : Finset G) (F : G → G → ℝ) : ℝ :=
  𝔼 u ∈ C, 𝔼 v ∈ C, matchedPairAverage L S (fun x y => F (x + u) (y + v))

theorem matchedIndependentAverage_eq_average (L S C : Finset G) (F : G → G → ℝ) :
    matchedIndependentAverage L S C F =
      matchedPairAverage L S (fun x y => 𝔼 u ∈ C, 𝔼 v ∈ C, F (x + u) (y + v)) := by
  unfold matchedIndependentAverage
  simp_rw [expect_matchedPairAverage]

variable [DecidableEq G]

theorem matchedIndependentAverage_eq_cells (L S C : Finset G) (a f g : G → ℝ) :
    matchedIndependentAverage L S C (fun x y => f x * g y * a (x + y)) =
      𝔼 z ∈ matchedCellSpace L S,
        bilinearIntegral (C.image (fun t => z.1 + t))
          (C.image (fun t => (-z.1 + z.2.1 + z.2.2) + t)) a f g := by
  rw [matchedIndependentAverage_eq_average, matchedPairAverage_eq_space]
  apply Finset.expect_congr rfl
  intro z _
  unfold bilinearIntegral
  rw [Finset.expect_image (fun _ _ _ _ h => add_left_cancel h)]
  apply Finset.expect_congr rfl
  intro u _
  rw [Finset.expect_image (fun _ _ _ _ h => add_left_cancel h)]

theorem matchedIndependentAverage_eq_restricted_cells (L S C : Finset G) (a f g : G → ℝ) :
    matchedIndependentAverage L S C (fun x y => f x * g y * a (x + y)) =
      𝔼 z ∈ matchedCellSpace L S,
        bilinearIntegral (C.image (fun t => z.1 + t))
          (C.image (fun t => (-z.1 + z.2.1 + z.2.2) + t)) a
          (Peeling.slice (C.image (fun t => z.1 + t)) f)
          (Peeling.slice (C.image (fun t => (-z.1 + z.2.1 + z.2.2) + t)) g) := by
  rw [matchedIndependentAverage_eq_cells]
  apply Finset.expect_congr rfl
  intro z _
  exact (bilinearIntegral_restrict _ _ a f g).symm

theorem expect_translated_cell (C : Finset G) (f : G → ℝ) (z : G) :
    (𝔼 x ∈ C.image (fun t => z + t), f x) = cellAverage C f z := by
  rw [Finset.expect_image (fun _ _ _ _ h => add_left_cancel h)]
  rfl

variable [Fintype G]

theorem abs_matchedIndependentAverage_sub_le
    (L S C : Finset G) (hL : L.Nonempty) (hS : S.Nonempty) (hC : C.Nonempty)
    (F : G → G → ℝ) {M etaL etaS : ℝ} (hM : 0 ≤ M) (hF : ∀ x y, |F x y| ≤ M)
    (hLshift : ∀ u ∈ C, (∑ x, |realUniformMass L (x - u) - realUniformMass L x|) ≤ etaL)
    (hSshift : ∀ u ∈ C, ∀ v ∈ C,
      (∑ x, |realUniformMass S (x - (u + v)) - realUniformMass S x|) ≤ etaS) :
    |matchedIndependentAverage L S C F - matchedPairAverage L S F| ≤ M * (etaL + etaS) := by
  calc
    _ = |(𝔼 u ∈ C, 𝔼 v ∈ C, matchedPairAverage L S (fun x y => F (x + u) (y + v))) -
        𝔼 _u ∈ C, 𝔼 _v ∈ C, matchedPairAverage L S F| := by
      rw [Finset.expect_const hC, Finset.expect_const hC]
      rfl
    _ ≤ M * (etaL + etaS) := by
      apply abs_expect_sub_expect_le C hC
      intro u hu
      apply abs_expect_sub_expect_le C hC
      intro v hv
      exact abs_matchedPairAverage_shift_sub_le L S hL hS F u v hM hF
        (hLshift u hu) (hSshift u hu v hv)

theorem matched_independent_cell_potential_le
    (L S C : Finset G) (hL : L.Nonempty) (hS : S.Nonempty) (hC : C.Nonempty)
    (f g : G → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ L → f x = 0) (hgsupport : ∀ x, x ∉ L → g x = 0) :
    (𝔼 z ∈ matchedCellSpace L S,
      ((𝔼 x ∈ C.image (fun t => z.1 + t), f x) *
        (𝔼 y ∈ C.image (fun t => (-z.1 + z.2.1 + z.2.2) + t), g y)) ^ (1 / 4 : ℝ)) ≤
      ((𝔼 x ∈ L, f x) * (𝔼 x ∈ L, g x)) ^ (1 / 4 : ℝ) := by
  simp_rw [expect_translated_cell]
  exact matched_cell_potential_le L S C hL hS hC f g hf hg hfsupport hgsupport

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G]

noncomputable def matchedIntegral (L S : Finset G) (a f g : G → ℝ) : ℝ :=
  matchedPairAverage L S (fun x y => f x * g y * a (x + y))

theorem matchedIntegral_sum_order (L S : Finset G) (a f g : G → ℝ) :
    matchedIntegral L S a f g =
      𝔼 s ∈ S, 𝔼 t ∈ S, 𝔼 r ∈ L, f r * g (-r + (s + t)) * a (s + t) := by
  unfold matchedIntegral matchedPairAverage
  rw [Finset.expect_comm L S]
  apply Finset.expect_congr rfl
  intro s _
  rw [Finset.expect_comm L S]
  apply Finset.expect_congr rfl
  intro t _
  apply Finset.expect_congr rfl
  intro r _
  dsimp only
  have heq : r + (-r + s + t) = s + t := by abel
  rw [heq, add_assoc (-r) s t]

theorem matchedIntegral_div_weights (L S : Finset G) (a f g : G → ℝ) (u v : ℝ) :
    matchedIntegral L S a (fun x => f x / u) (fun y => g y / v) =
      matchedIntegral L S a f g / (u * v) := by
  simp only [matchedIntegral_sum_order]
  have heq (r s t : G) : f r / u * (g (-r + (s + t)) / v) * a (s + t) =
      (f r * g (-r + (s + t)) * a (s + t)) / (u * v) := by ring
  simp_rw [heq, ← Finset.expect_div]

variable [Fintype G] [DecidableEq G]

omit [DecidableEq G] in
theorem matchedIntegral_eq_convolution (L S : Finset G) (a f g : G → ℝ)
    (hfsupport : ∀ x, x ∉ L → f x = 0) :
    matchedIntegral L S a f g =
      𝔼 s ∈ S, 𝔼 t ∈ S, a (s + t) * LocalConvolution.convolution L f g (s + t) := by
  rw [matchedIntegral_sum_order]
  apply Finset.expect_congr rfl
  intro s _
  apply Finset.expect_congr rfl
  intro t _
  have heq (r : G) : -r + (s + t) = (s + t) - r := by abel
  simp_rw [heq]
  rw [← Finset.expect_mul, Peeling.expect_eq_total_div L (fun r => f r * g ((s + t) - r))]
  · unfold LocalConvolution.convolution
    ring
  · intro r hr
    rw [hfsupport r hr, zero_mul]

theorem abs_matchedIntegral_restrict_sub_le
    (L S : Finset G) (hsymm : -L = L) (hS : S.Nonempty) (a f g : G → ℝ)
    {M eta : ℝ} (hM : 0 ≤ M) (ha : ∀ x, |a x| ≤ M)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hTV : ∀ s ∈ S, ∀ t ∈ S,
      (∑ x, |realUniformMass L (x - (s + t)) - realUniformMass L x|) ≤ eta) :
    |matchedIntegral L S a f g - matchedIntegral L S a (Peeling.slice L f) (Peeling.slice L g)| ≤
      M * eta := by
  simp only [matchedIntegral_sum_order]
  apply abs_expect_sub_expect_le S hS
  intro s hs
  apply abs_expect_sub_expect_le S hS
  intro t ht
  have htrunc :
      (𝔼 r ∈ L, Peeling.slice L f r * Peeling.slice L g (-r + (s + t)) * a (s + t)) =
        𝔼 r ∈ L, if -r + (s + t) ∈ L then f r * g (-r + (s + t)) * a (s + t) else 0 := by
    apply Finset.expect_congr rfl
    intro r hr
    by_cases hy : -r + (s + t) ∈ L <;> simp [Peeling.slice, hr, hy]
  rw [htrunc]
  exact abs_reflected_restriction_le L hsymm (fun r y => f r * g y * a (s + t)) (s + t)
    hM (fun r y => abs_unit_weighted_mul_le (hf r) (hg y) (ha (s + t))) (hTV s hs t ht)

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem matched_flat_integral_le (L S : Finset G) (A B f g : G → ℝ)
    {q : ℕ} (hq : 0 < q) {epsilon delta W M eta : ℝ}
    (hW : 0 ≤ W) (hM : 0 ≤ M) (hepsilon : 0 ≤ epsilon)
    (hdelta : 0 < delta) (hdelta2 : delta ≤ 1 / 2)
    (hcoeff : 1 + 2 * delta ≤ (1 + epsilon) * (1 - 2 * delta))
    (hA : ∀ x, 0 ≤ A x ∧ A x ≤ W) (hB : ∀ x, 0 ≤ B x ∧ B x ≤ W)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ M)
    (hfsupport : ∀ x, x ∉ L → f x = 0) (hfmass : (∑ x, f x) / (L.card : ℝ) = 1)
    (hflat : LocalConvolution.sumLp S (fun x => LocalConvolution.convolution L f g x - 1) q ≤ delta)
    (hmean : (𝔼 s ∈ S, 𝔼 t ∈ S, (A (s + t) - B (s + t))) ≤ eta) :
    matchedIntegral L S (fun x => A x - (1 + epsilon) * B x) f g ≤
      (1 + 2 * delta) * eta + W * (M + 2) * (1 / 2 : ℝ) ^ q := by
  have h := flat_weighted_average_le (S ×ˢ S)
    (fun z => A (z.1 + z.2)) (fun z => B (z.1 + z.2))
    (fun z => LocalConvolution.convolution L f g (z.1 + z.2)) hq
    hW hM hepsilon hdelta hdelta2 hcoeff (fun z _ => hA _) (fun z _ => hB _)
    (fun z _ => ⟨LocalConvolution.convolution_nonneg L f g hf (fun x => (hg x).1) _,
      LocalConvolution.convolution_le_of_mass L f g hf (fun x => (hg x).2) hfmass _⟩)
    hflat (by simpa only [Finset.expect_product] using hmean)
  rw [matchedIntegral_eq_convolution L S _ f g hfsupport]
  simpa only [Finset.expect_product] using h

theorem matched_flat_integral_le_normalized (L S : Finset G) (A B f g : G → ℝ)
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) {q : ℕ} (hq : 0 < q)
    {epsilon delta W M eta : ℝ} (hW : 0 ≤ W) (hM : 0 ≤ M) (hepsilon : 0 ≤ epsilon)
    (hdelta : 0 < delta) (hdelta2 : delta ≤ 1 / 2)
    (hcoeff : 1 + 2 * delta ≤ (1 + epsilon) * (1 - 2 * delta))
    (hA : ∀ x, 0 ≤ A x ∧ A x ≤ W) (hB : ∀ x, 0 ≤ B x ∧ B x ≤ W)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (hgcap : ∀ x, g x / v ≤ M)
    (hfsupport : ∀ x, x ∉ L → f x = 0) (hfmean : (𝔼 x ∈ L, f x) = u)
    (hflat : LocalConvolution.sumLp S
      (fun x => LocalConvolution.convolution L (fun y => f y / u) (fun y => g y / v) x - 1) q ≤ delta)
    (hmean : (𝔼 s ∈ S, 𝔼 t ∈ S, (A (s + t) - B (s + t))) ≤ eta) :
    matchedIntegral L S (fun x => A x - (1 + epsilon) * B x) f g ≤
      (u * v) * ((1 + 2 * delta) * eta + W * (M + 2) * (1 / 2 : ℝ) ^ q) := by
  have hnorm := LocalConvolution.normalized_mass_one L f hfsupport hu hfmean
  have h := matched_flat_integral_le L S A B (fun x => f x / u) (fun x => g x / v)
    hq hW hM hepsilon hdelta hdelta2 hcoeff hA hB
    (fun x => div_nonneg (hf x) hu.le) (fun x => ⟨div_nonneg (hg x) hv.le, hgcap x⟩)
    (fun x hx => by rw [hfsupport x hx, zero_div]) hnorm hflat hmean
  rw [matchedIntegral_div_weights] at h
  simpa only [mul_comm] using (div_le_iff₀ (mul_pos hu hv)).mp h

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G]

noncomputable def parentMatchedAverage (A B L S : Finset G) (F : G → G → ℝ) : ℝ :=
  𝔼 x ∈ A, 𝔼 y ∈ B, matchedPairAverage L S (fun r q => F (x + r) (y + q))

theorem parentMatchedAverage_eq_average (A B L S : Finset G) (F : G → G → ℝ) :
    parentMatchedAverage A B L S F =
      matchedPairAverage L S (fun r q => 𝔼 x ∈ A, 𝔼 y ∈ B, F (x + r) (y + q)) := by
  unfold parentMatchedAverage
  simp_rw [expect_matchedPairAverage]

theorem parentMatchedAverage_eq_integrals (A B L S : Finset G) (a f g : G → ℝ) :
    parentMatchedAverage A B L S (fun x y => f x * g y * a (x + y)) =
      𝔼 x ∈ A, 𝔼 y ∈ B, matchedIntegral L S (fun z => a (x + y + z))
        (fun r => f (x + r)) (fun q => g (y + q)) := by
  unfold parentMatchedAverage
  apply Finset.expect_congr rfl
  intro x _
  apply Finset.expect_congr rfl
  intro y _
  unfold matchedIntegral
  apply congrArg (matchedPairAverage L S)
  funext r q
  dsimp only
  rw [show (x + r) + (y + q) = x + y + (r + q) by abel]

variable [DecidableEq G]

noncomputable def parentTruncatedIntegral (A B L S : Finset G) (a f g : G → ℝ) : ℝ :=
  𝔼 x ∈ A, 𝔼 y ∈ B, matchedIntegral L S (fun z => a (x + y + z))
    (Peeling.slice L (fun r => f (x + r))) (Peeling.slice L (fun q => g (y + q)))

variable [Fintype G]

theorem abs_parentMatchedAverage_sub_le
    (A B L S : Finset G) (hA : A.Nonempty) (hB : B.Nonempty) (hL : L.Nonempty) (hS : S.Nonempty)
    (F : G → G → ℝ) {M etaA etaB : ℝ} (hM : 0 ≤ M) (hF : ∀ x y, |F x y| ≤ M)
    (hAshift : ∀ r ∈ L, (∑ x, |realUniformMass A (x - r) - realUniformMass A x|) ≤ etaA)
    (hBshift : ∀ r ∈ L, ∀ s ∈ S, ∀ t ∈ S,
      (∑ y, |realUniformMass B (y - (-r + s + t)) - realUniformMass B y|) ≤ etaB) :
    |parentMatchedAverage A B L S F - 𝔼 x ∈ A, 𝔼 y ∈ B, F x y| ≤ M * (etaA + etaB) := by
  rw [parentMatchedAverage_eq_average]
  calc
    _ = |matchedPairAverage L S (fun r q => 𝔼 x ∈ A, 𝔼 y ∈ B, F (x + r) (y + q)) -
        matchedPairAverage L S (fun _ _ => 𝔼 x ∈ A, 𝔼 y ∈ B, F x y)| := by
      rw [matchedPairAverage_const L S hL hS]
    _ ≤ M * (etaA + etaB) := by
      unfold matchedPairAverage
      apply abs_expect_sub_expect_le L hL
      intro r hr
      apply abs_expect_sub_expect_le S hS
      intro s hs
      apply abs_expect_sub_expect_le S hS
      intro t ht
      exact abs_expect_pair_add_sub_le A B hA hB F r (-r + s + t) hM hF
        (hAshift r hr) (hBshift r hr s hs t ht)

theorem abs_parentMatchedAverage_sub_truncated_le
    (A B L S : Finset G) (hA : A.Nonempty) (hB : B.Nonempty) (hsymm : -L = L) (hS : S.Nonempty)
    (a f g : G → ℝ) {M etaL : ℝ} (hM : 0 ≤ M) (ha : ∀ x, |a x| ≤ M)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hTV : ∀ s ∈ S, ∀ t ∈ S,
      (∑ x, |realUniformMass L (x - (s + t)) - realUniformMass L x|) ≤ etaL) :
    |parentMatchedAverage A B L S (fun x y => f x * g y * a (x + y)) -
      parentTruncatedIntegral A B L S a f g| ≤ M * etaL := by
  rw [parentMatchedAverage_eq_integrals]
  unfold parentTruncatedIntegral
  apply abs_expect_sub_expect_le A hA
  intro x _
  apply abs_expect_sub_expect_le B hB
  intro y _
  exact abs_matchedIntegral_restrict_sub_le L S hsymm hS _ _ _ hM
    (fun z => ha (x + y + z)) (fun r => hf (x + r)) (fun q => hg (y + q)) hTV

theorem parent_integral_truncated_comparison
    (A B L S : Finset G) (hA : A.Nonempty) (hB : B.Nonempty) (hL : L.Nonempty) (hS : S.Nonempty)
    (hsymm : -L = L) (a f g : G → ℝ) {M etaA etaB etaL : ℝ} (hM : 0 ≤ M)
    (ha : ∀ x, |a x| ≤ M) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hAshift : ∀ r ∈ L, (∑ x, |realUniformMass A (x - r) - realUniformMass A x|) ≤ etaA)
    (hBshift : ∀ r ∈ L, ∀ s ∈ S, ∀ t ∈ S,
      (∑ y, |realUniformMass B (y - (-r + s + t)) - realUniformMass B y|) ≤ etaB)
    (hLshift : ∀ s ∈ S, ∀ t ∈ S,
      (∑ x, |realUniformMass L (x - (s + t)) - realUniformMass L x|) ≤ etaL) :
    |bilinearIntegral A B a f g - parentTruncatedIntegral A B L S a f g| ≤
      M * (etaA + etaB + etaL) := by
  have hfirst := abs_parentMatchedAverage_sub_le A B L S hA hB hL hS
    (fun x y => f x * g y * a (x + y)) hM
    (fun x y => abs_unit_weighted_mul_le (hf x) (hg y) (ha (x + y))) hAshift hBshift
  have hsecond := abs_parentMatchedAverage_sub_truncated_le A B L S hA hB hsymm hS a f g
    hM ha hf hg hLshift
  calc
    _ ≤ |bilinearIntegral A B a f g -
          parentMatchedAverage A B L S (fun x y => f x * g y * a (x + y))| +
        |parentMatchedAverage A B L S (fun x y => f x * g y * a (x + y)) -
          parentTruncatedIntegral A B L S a f g| := abs_sub_le _ _ _
    _ ≤ M * (etaA + etaB) + M * etaL :=
      add_le_add (by simpa only [bilinearIntegral, abs_sub_comm] using hfirst) hsecond
    _ = _ := by ring

theorem parentTruncatedIntegral_eq_convolution (A B L S : Finset G) (a f g : G → ℝ) :
    parentTruncatedIntegral A B L S a f g =
      𝔼 x ∈ A, 𝔼 y ∈ B, 𝔼 s ∈ S, 𝔼 t ∈ S, a (x + y + (s + t)) *
        LocalConvolution.convolution L (Peeling.slice L (fun r => f (x + r)))
          (Peeling.slice L (fun q => g (y + q))) (s + t) := by
  unfold parentTruncatedIntegral
  apply Finset.expect_congr rfl
  intro x _
  apply Finset.expect_congr rfl
  intro y _
  exact matchedIntegral_eq_convolution L S _ _ _ (fun r hr => by simp [Peeling.slice, hr])

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def centerSlice (L : Finset G) (f : G → ℝ) (x : G) : G → ℝ :=
  Peeling.slice L (fun r => f (x + r))

theorem centerSlice_bounds (L : Finset G) (f : G → ℝ)
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (x r : G) :
    0 ≤ centerSlice L f x r ∧ centerSlice L f x r ≤ 1 := by
  exact ⟨translated_slice_nonneg L f (fun t => (hf t).1) x r,
    (translated_slice_le L f (fun t => (hf t).1) x r).trans (hf (x + r)).2⟩

theorem centerSlice_supported (L : Finset G) (f : G → ℝ) (x : G) :
    ∀ r, r ∉ L → centerSlice L f x r = 0 := by
  intro r hr
  simp only [centerSlice, Peeling.slice, hr, ite_false]

theorem centerSlice_mean (L : Finset G) (f : G → ℝ) (x : G) :
    (𝔼 r ∈ L, centerSlice L f x r) = cellAverage L f x :=
  expect_translated_slice L f x

theorem centerSlice_normalized_cap (L : Finset G) (f : G → ℝ)
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (x : G) {U c₀ M : ℝ}
    (hU : 0 < U) (hc₀ : 0 < c₀) (hM : 0 ≤ M)
    (hcap : 1 ≤ M * (c₀ * U)) (hlower : c₀ * U ≤ cellAverage L f x) (r : G) :
    centerSlice L f x r / cellAverage L f x ≤ M := by
  have hmean : 0 < cellAverage L f x := (mul_pos hc₀ hU).trans_le hlower
  apply (div_le_iff₀ hmean).mpr
  exact (centerSlice_bounds L f hf x r).2.trans
    (hcap.trans (mul_le_mul_of_nonneg_left hlower hM))

noncomputable def centerPotential (L : Finset G) (f g : G → ℝ) (z : G × G) : ℝ :=
  (cellAverage L f z.1 * cellAverage L g z.2) ^ (1 / 4 : ℝ)

noncomputable def centerMatchedIntegral (L S : Finset G) (a f g : G → ℝ) (z : G × G) : ℝ :=
  matchedIntegral L S (fun r => a (z.1 + z.2 + r)) (centerSlice L f z.1) (centerSlice L g z.2)

noncomputable def centerChildIntegral (L S : Finset G) (a f g : G → ℝ)
    (z : G × G) (C : Finset G) : ℝ :=
  𝔼 t ∈ matchedCellSpace L S,
    bilinearIntegral (C.image (fun r => t.1 + r))
      (C.image (fun r => (-t.1 + t.2.1 + t.2.2) + r))
      (fun r => a (z.1 + z.2 + r)) (centerSlice L f z.1) (centerSlice L g z.2)

noncomputable def centerChildPotential (L S : Finset G) (f g : G → ℝ)
    (z : G × G) (C : Finset G) : ℝ :=
  𝔼 t ∈ matchedCellSpace L S,
    (matchedFirstCell C (centerSlice L f z.1) t *
      matchedSecondCell C (centerSlice L g z.2) t) ^ (1 / 4 : ℝ)

theorem centerMatchedIntegral_mean (B L S : Finset G) (a f g : G → ℝ) :
    (𝔼 z ∈ B ×ˢ B, centerMatchedIntegral L S a f g z) =
      parentTruncatedIntegral B B L S a f g := by
  rw [Finset.expect_product]
  rfl

omit [DecidableEq G] in
theorem centerPotential_nonneg (L : Finset G) (f g : G → ℝ)
    (hf : ∀ r, 0 ≤ f r) (hg : ∀ r, 0 ≤ g r) (z : G × G) :
    0 ≤ centerPotential L f g z :=
  Real.rpow_nonneg (mul_nonneg (cellAverage_nonneg L f hf z.1) (cellAverage_nonneg L g hg z.2)) _

variable [Fintype G]

theorem centerPotential_mean_le (B L : Finset G) (hB : B.Nonempty) (hL : L.Nonempty)
    (f g : G → ℝ) (hf : ∀ r, 0 ≤ f r) (hg : ∀ r, 0 ≤ g r)
    (hfsupport : ∀ r, r ∉ B → f r = 0) (hgsupport : ∀ r, r ∉ B → g r = 0) :
    (𝔼 z ∈ B ×ˢ B, centerPotential L f g z) ≤
      ((𝔼 r ∈ B, f r) * (𝔼 r ∈ B, g r)) ^ (1 / 4 : ℝ) := by
  simpa only [Finset.expect_product, centerPotential] using
    parent_cell_potential_le B L hB hL f g hf hg hfsupport hgsupport

theorem centerChildPotential_le (L S C : Finset G)
    (hL : L.Nonempty) (hS : S.Nonempty) (hC : C.Nonempty)
    (f g : G → ℝ) (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1)
    (z : G × G) : centerChildPotential L S f g z C ≤ centerPotential L f g z := by
  have h := matched_cell_potential_le L S C hL hS hC (centerSlice L f z.1) (centerSlice L g z.2)
    (fun r => (centerSlice_bounds L f hf z.1 r).1) (fun r => (centerSlice_bounds L g hg z.2 r).1)
    (centerSlice_supported L f z.1) (centerSlice_supported L g z.2)
  simpa only [centerChildPotential, centerPotential, centerSlice_mean] using h

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem bilinearIntegral_translated_centerSlices (C : Finset G) (a f g : G → ℝ) (x y : G) :
    bilinearIntegral (C.image (fun r => x + r)) (C.image (fun r => y + r)) a f g =
      bilinearIntegral C C (fun r => a (x + y + r)) (centerSlice C f x) (centerSlice C g y) := by
  rw [bilinearIntegral_translate]
  exact (bilinearIntegral_restrict C C (fun r => a (x + y + r))
    (fun r => f (x + r)) (fun r => g (y + r))).symm

theorem centerChildIntegral_eq_rebased (L S C : Finset G) (a f g : G → ℝ) (z : G × G) :
    centerChildIntegral L S a f g z C =
      𝔼 t ∈ matchedCellSpace L S,
        bilinearIntegral C C (fun r => a (z.1 + z.2 + (t.2.1 + t.2.2) + r))
          (centerSlice C (centerSlice L f z.1) t.1)
          (centerSlice C (centerSlice L g z.2) (-t.1 + t.2.1 + t.2.2)) := by
  unfold centerChildIntegral
  apply Finset.expect_congr rfl
  intro t _
  rw [bilinearIntegral_translated_centerSlices]
  congr 1
  funext r
  congr 1
  abel

theorem centerChildPotential_eq_rebased (L S C : Finset G) (f g : G → ℝ) (z : G × G) :
    centerChildPotential L S f g z C =
      𝔼 t ∈ matchedCellSpace L S,
        ((𝔼 r ∈ C, centerSlice C (centerSlice L f z.1) t.1 r) *
          (𝔼 r ∈ C, centerSlice C (centerSlice L g z.2) (-t.1 + t.2.1 + t.2.2) r)) ^ (1 / 4 : ℝ) := by
  simp only [centerSlice_mean, centerChildPotential, matchedFirstCell, matchedSecondCell]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

def CellBilinearBound (C : Finset G) (a : G → ℝ) (T : ℝ) : Prop :=
  ∀ origin : G, ∀ f g : G → ℝ,
    (∀ x, 0 ≤ f x ∧ f x ≤ 1) → (∀ x, 0 ≤ g x ∧ g x ≤ 1) →
    (∀ x, x ∉ C → f x = 0) → (∀ x, x ∉ C → g x = 0) →
    bilinearIntegral C C (fun x => a (origin + x)) f g ≤
      T * ((𝔼 x ∈ C, f x) * (𝔼 x ∈ C, g x)) ^ (1 / 4 : ℝ)

theorem CellBilinearBound.mono {C : Finset G} {a : G → ℝ} {T U : ℝ}
    (h : CellBilinearBound C a T) (hTU : T ≤ U) : CellBilinearBound C a U := by
  intro origin f g hf hg hfs hgs
  exact (h origin f g hf hg hfs hgs).trans (mul_le_mul_of_nonneg_right hTU
    (Real.rpow_nonneg (mul_nonneg (Finset.expect_nonneg (fun x _ => (hf x).1))
      (Finset.expect_nonneg (fun x _ => (hg x).1))) _))

theorem cellBilinearBound_of_upper (C : Finset G) (hC : C.Nonempty)
    (a : G → ℝ) {M : ℝ} (hM : 0 ≤ M) (ha : ∀ x, a x ≤ M) :
    CellBilinearBound C a M := by
  intro origin f g hf hg _ _
  have hu : 0 ≤ 𝔼 x ∈ C, f x := Finset.expect_nonneg (fun x _ => (hf x).1)
  have hv : 0 ≤ 𝔼 x ∈ C, g x := Finset.expect_nonneg (fun x _ => (hg x).1)
  have hu1 : (𝔼 x ∈ C, f x) ≤ 1 :=
    (Finset.expect_le_expect (fun x (_ : x ∈ C) => (hf x).2)).trans_eq (Finset.expect_const hC 1)
  have hv1 : (𝔼 x ∈ C, g x) ≤ 1 :=
    (Finset.expect_le_expect (fun x (_ : x ∈ C) => (hg x).2)).trans_eq (Finset.expect_const hC 1)
  have hprod : (𝔼 x ∈ C, f x) * (𝔼 x ∈ C, g x) ≤ 1 := by nlinarith
  have hpower := Real.self_le_rpow_of_le_one (mul_nonneg hu hv) hprod (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have h := bilinearIntegral_le C C (fun x => a (origin + x)) f g
    (fun x => ha (origin + x)) (fun x => (hf x).1) (fun x => (hg x).1)
  exact h.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpower hM)

variable [DecidableEq G]

theorem translated_integral_le_of_cellBilinearBound
    (C : Finset G) (a f g : G → ℝ) (origin x y : G) {T : ℝ}
    (hbound : CellBilinearBound C a T)
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1) :
    bilinearIntegral (C.image (fun r => x + r)) (C.image (fun r => y + r))
        (fun r => a (origin + r)) f g ≤
      T * (cellAverage C f x * cellAverage C g y) ^ (1 / 4 : ℝ) := by
  rw [bilinearIntegral_translated_centerSlices]
  have h := hbound (origin + (x + y)) (centerSlice C f x) (centerSlice C g y)
    (centerSlice_bounds C f hf x) (centerSlice_bounds C g hg y)
    (centerSlice_supported C f x) (centerSlice_supported C g y)
  simpa only [centerSlice_mean, add_assoc] using h

theorem centerChildIntegral_le_of_cellBilinearBound
    (L S C : Finset G) (a f g : G → ℝ) (origin : G) (z : G × G) {T : ℝ}
    (hbound : CellBilinearBound C a T)
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1) :
    centerChildIntegral L S (fun r => a (origin + r)) f g z C ≤
      T * centerChildPotential L S f g z C := by
  rw [centerChildIntegral_eq_rebased, centerChildPotential_eq_rebased]
  calc
    _ ≤ 𝔼 t ∈ matchedCellSpace L S,
        T * ((𝔼 r ∈ C, centerSlice C (centerSlice L f z.1) t.1 r) *
          (𝔼 r ∈ C, centerSlice C (centerSlice L g z.2) (-t.1 + t.2.1 + t.2.2) r)) ^ (1 / 4 : ℝ) := by
      apply Finset.expect_le_expect
      intro t _
      have h := hbound (origin + (z.1 + z.2 + (t.2.1 + t.2.2)))
        (centerSlice C (centerSlice L f z.1) t.1)
        (centerSlice C (centerSlice L g z.2) (-t.1 + t.2.1 + t.2.2))
        (centerSlice_bounds C _ (centerSlice_bounds L f hf z.1) t.1)
        (centerSlice_bounds C _ (centerSlice_bounds L g hg z.2) (-t.1 + t.2.1 + t.2.2))
        (centerSlice_supported C _ t.1)
        (centerSlice_supported C _ (-t.1 + t.2.1 + t.2.2))
      simpa only [add_assoc] using h
    _ = _ := (Finset.mul_expect _ _ T).symm

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] {I : Type*}

theorem finite_cell_refinement (carrier : I → Finset G) (family : ℕ → I → Prop)
    (a : G → ℝ) (n : ℕ) {W rho error : ℝ}
    (hW : 0 ≤ W) (hrho : 0 ≤ rho) (hrho1 : rho < 1) (herror : 0 ≤ error)
    (ha : ∀ r, a r ≤ W)
    (hnonempty : ∀ j C, family j C → (carrier C).Nonempty)
    (hstep : ∀ j, j < n → ∀ T : ℝ, 0 ≤ T →
      (∀ C, family (j + 1) C → CellBilinearBound (carrier C) a T) →
      ∀ C, family j C → CellBilinearBound (carrier C) a (rho * T + error)) :
    ∀ C, family 0 C →
      CellBilinearBound (carrier C) a (rho ^ n * W + error / (1 - rho)) := by
  have hgap : 0 < 1 - rho := by linarith
  have herr : 0 ≤ error / (1 - rho) := div_nonneg herror hgap.le
  have aux : ∀ k j : ℕ, j + k ≤ n → ∀ C, family j C →
      CellBilinearBound (carrier C) a (rho ^ k * W + error / (1 - rho)) := by
    intro k
    induction k with
    | zero =>
      intro j _ C hC
      apply (cellBilinearBound_of_upper (carrier C) (hnonempty j C hC) a hW ha).mono
      simpa only [pow_zero, one_mul] using le_add_of_nonneg_right herr
    | succ k ih =>
      intro j hj C hC
      have hT : 0 ≤ rho ^ k * W + error / (1 - rho) :=
        add_nonneg (mul_nonneg (pow_nonneg hrho _) hW) herr
      have h := hstep j (by omega) _ hT
        (fun D hD => ih (j + 1) (by omega) D hD) C hC
      apply h.mono
      apply le_of_eq
      rw [pow_succ]
      field_simp
      ring
  exact aux n 0 (by omega)

theorem refinement_coefficient_le {rho W error Q R : ℝ} {n : ℕ}
    (hrho : 0 ≤ rho) (hrho1 : rho < 1) (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q)
    (hdepth : Q + R ≤ (1 - rho) * n)
    (herror : error ≤ (1 - rho) * Real.exp (-R)) :
    rho ^ n * W + error / (1 - rho) ≤ 2 * Real.exp (-R) := by
  have hgap : 0 < 1 - rho := by linarith
  have hrhoExp : rho ≤ Real.exp (-(1 - rho)) := by
    linarith [Real.add_one_le_exp (-(1 - rho))]
  have hdecay : rho ^ n * W ≤ Real.exp (-R) := by
    calc
      _ ≤ (Real.exp (-(1 - rho))) ^ n * Real.exp Q :=
        mul_le_mul (pow_le_pow_left₀ hrho hrhoExp _) hWcap hW (by positivity)
      _ = Real.exp ((n : ℝ) * (-(1 - rho)) + Q) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hnoise : error / (1 - rho) ≤ Real.exp (-R) :=
    (div_le_iff₀ hgap).mpr (by simpa only [mul_comm] using herror)
  linarith

theorem exists_refinement_depth {rho Q R : ℝ}
    (hrho1 : rho < 1) (hQ : 0 ≤ Q) (hR : 0 ≤ R) :
    ∃ n : ℕ, Q + R ≤ (1 - rho) * n ∧ (n : ℝ) ≤ (Q + R) / (1 - rho) + 1 := by
  have hgap : 0 < 1 - rho := by linarith
  have hnonneg : 0 ≤ (Q + R) / (1 - rho) := div_nonneg (add_nonneg hQ hR) hgap.le
  refine ⟨⌈(Q + R) / (1 - rho)⌉₊, ?_, (Nat.ceil_lt_add_one hnonneg).le⟩
  have h := Nat.le_ceil ((Q + R) / (1 - rho))
  exact (div_le_iff₀ hgap).mp h |>.trans_eq (mul_comm _ _)

end Erdos3.CellRefinement

end

end OAI
