import GowersSzemeredi.Proofs16BipartiteQuasirandom

/-! Empty rectangles are controlled directly by the box discrepancy.
This first-moment bound avoids the squared density loss of a variance bound. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem box_empty_rectangle_card {X Y : Type*} [Fintype X] [Fintype Y]
    (E : X → Y → Prop) (U : Finset X) (Z : Finset Y) {delta epsilon : Real}
    (hd : 0 ≤ delta) (he : 0 ≤ epsilon)
    (hbox : boxSum (fun x y => (if E x y then (1 : Real) else 0)-delta) ≤
      epsilon^4*(Fintype.card X : Real)^2*(Fintype.card Y : Real)^2)
    (hempty : ∀ x ∈ U, ∀ y ∈ Z, ¬ E x y) :
    delta*(U.card : Real)*(Z.card : Real) ≤ epsilon*Fintype.card X*Fintype.card Y := by
  have h := abs_box_correlation_le (fun x y => (if E x y then (1 : Real) else 0)-delta)
    he hbox (fun x => if x ∈ U then 1 else 0) (fun y => if y ∈ Z then 1 else 0)
    (fun x => by split_ifs <;> norm_num) (fun y => by split_ifs <;> norm_num)
  have ht (x : X) (y : Y) : ((if E x y then (1 : Real) else 0)-delta)*
      (if x ∈ U then 1 else 0)*(if y ∈ Z then 1 else 0) =
      if x ∈ U then (if y ∈ Z then -delta else 0) else 0 := by
    by_cases hx : x ∈ U <;> by_cases hy : y ∈ Z
    · simp [hx,hy,hempty x hx y hy]
    · simp [hx,hy]
    · simp [hx,hy]
    · simp [hx,hy]
  simp_rw [ht] at h
  have hs : (∑ x : X, ∑ y : Y, if x ∈ U then (if y ∈ Z then -delta else 0) else 0) =
      -(delta*(U.card : Real)*(Z.card : Real)) := by
    simp only [Finset.sum_ite_irrel,Finset.sum_const_zero]
    simp
    ring
  rw [hs,abs_neg,abs_of_nonneg (by positivity)] at h
  exact h

theorem box_empty_finset_rectangle_card {X Y : Type*} [Fintype X] [Fintype Y]
    (E : X → Y → Prop) (B U : Finset X) (C Z : Finset Y)
    (hU : U ⊆ B) (hZ : Z ⊆ C) {delta epsilon : Real}
    (hd : 0 ≤ delta) (he : 0 ≤ epsilon)
    (hbox : boxSum (fun (x : ↥B) (y : ↥C) => (if E x y then (1 : Real) else 0)-delta) ≤
      epsilon^4*(B.card : Real)^2*(C.card : Real)^2)
    (hempty : ∀ x ∈ U, ∀ y ∈ Z, ¬ E x y) :
    delta*(U.card : Real)*(Z.card : Real) ≤ epsilon*B.card*C.card := by
  let liftU : ↥U ↪ ↥B := ⟨fun x => ⟨x,hU x.property⟩,
    fun x y h => Subtype.ext (congrArg (fun z : ↥B => (z : X)) h)⟩
  let liftZ : ↥Z ↪ ↥C := ⟨fun y => ⟨y,hZ y.property⟩,
    fun x y h => Subtype.ext (congrArg (fun z : ↥C => (z : Y)) h)⟩
  have h := box_empty_rectangle_card (fun (x : ↥B) (y : ↥C) => E x y)
    (Finset.univ.map liftU) (Finset.univ.map liftZ) hd he
    (by simpa only [Fintype.card_coe] using hbox) (by
      intro x hx y hy
      obtain ⟨u,_,rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨z,_,rfl⟩ := Finset.mem_map.mp hy
      exact hempty u u.property z z.property)
  simpa only [Finset.card_map,Finset.card_univ,Fintype.card_coe] using h

end LeanProofs.GowersSzemeredi
