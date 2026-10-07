import OAI.Combinatorics.Progressions.Estimates.CopiedLayerSpace

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def coordinateCopySum {C J R : Type*} [Fintype C]
    [DecidableEq J] [CommRing R] (label : C → J) : (C → R) →ₗ[R] (J → R) where
  toFun x j := ∑ c, if label c = j then x c else 0
  map_add' x y := by
    ext j
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> simp
  map_smul' r x := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> simp

@[simp] theorem coordinateCopySum_apply {C J R : Type*} [Fintype C]
    [DecidableEq J] [CommRing R] (label : C → J) (x : C → R) (j : J) :
    coordinateCopySum label x j = ∑ c, if label c = j then x c else 0 := rfl

theorem coordinateCopySum_sum {C D J R : Type*} [Fintype C] [Fintype D]
    [DecidableEq J] [CommRing R] (a : C → J) (b : D → J) (x : C → R) (y : D → R) :
    coordinateCopySum (Sum.elim a b) (Sum.elim x y) =
      coordinateCopySum a x + coordinateCopySum b y := by
  ext j
  simp only [coordinateCopySum_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Pi.add_apply]
  rfl

theorem coordinateCopySum_abs_le {C J : Type*} [Fintype C] [DecidableEq J]
    (label : C → J) {x : C → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (hx : ∀ c, |x c| ≤ δ) (j : J) :
    |coordinateCopySum label x j| ≤ Fintype.card C * δ := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ c, |if label c = j then x c else 0|) ≤ ∑ _c : C, δ := by
      apply Finset.sum_le_sum
      intro c _
      split_ifs <;> simp_all
    _ = _ := by simp

theorem coordinateCopySum_intCast {C J : Type*} [Fintype C] [DecidableEq J]
    (label : C → J) (x : C → ℤ) (j : J) :
    coordinateCopySum label (fun c => (x c : ℝ)) j =
      ((coordinateCopySum (R := ℤ) label x j : ℤ) : ℝ) := by
  simp only [coordinateCopySum_apply, Int.cast_sum, Int.cast_ite, Int.cast_zero]

theorem coordinateCopySum_map {C J R S : Type*} [Fintype C] [DecidableEq J]
    [CommRing R] [CommRing S] (label : C → J) (f : R →+* S) (x : C → R) (j : J) :
    f (coordinateCopySum label x j) = coordinateCopySum label (fun c => f (x c)) j := by
  simp only [coordinateCopySum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp

theorem coordinateCopySum_polynomial_degree {C J I R : Type*} [Fintype C] [DecidableEq J]
    [CommRing R] (label : C → J) (p : C → MvPolynomial I R) {d : ℕ}
    (hp : ∀ c, (p c).totalDegree ≤ d) (j : J) :
    (coordinateCopySum label p j).totalDegree ≤ d := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro c _
  split_ifs
  · exact hp c
  · simp

end Erdos3

end

end OAI
