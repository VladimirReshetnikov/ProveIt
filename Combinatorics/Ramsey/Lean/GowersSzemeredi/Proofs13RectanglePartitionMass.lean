import GowersSzemeredi.Proofs13DenseRectangleSelection
import GowersSzemeredi.Proofs05IntegerPartitionBounds

/-! Exact mass bookkeeping for product partitions and their intersections
with a dense subset. No large-modulus or Fourier assumptions are used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem IsPartition.inter_subset {X : Type*} [DecidableEq X] {M : Nat}
    {P : Fin M → Finset X} {S : Finset X} (hP : IsPartition P S)
    (B : Finset X) (hB : B ⊆ S) : IsPartition (fun i => P i ∩ B) B := by
  constructor
  · intro x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := (hP.1 x).mp (hB hx)
      exact ⟨i, Finset.mem_inter.mpr ⟨hi, hx⟩⟩
    · rintro ⟨i, hi⟩
      exact (Finset.mem_inter.mp hi).2
  · intro i j hij
    exact (hP.2 i j hij).mono Finset.inter_subset_left Finset.inter_subset_left

theorem IsPartition.product_left {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {M : Nat} {P : Fin M → Finset X} {S : Finset X} (hP : IsPartition P S)
    (T : Finset Y) : IsPartition (fun i => (P i).product T) (S.product T) := by
  constructor
  · intro z
    rcases z with ⟨x, y⟩
    constructor
    · intro hz
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hz
      obtain ⟨i, hi⟩ := (hP.1 x).mp hx
      exact ⟨i, Finset.mem_product.mpr ⟨hi, hy⟩⟩
    · rintro ⟨i, hz⟩
      obtain ⟨hi, hy⟩ := Finset.mem_product.mp hz
      exact Finset.mem_product.mpr ⟨(hP.1 x).mpr ⟨i, hi⟩, hy⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro z hzi hzj
    exact Finset.disjoint_left.mp (hP.2 i j hij)
      (Finset.mem_product.mp hzi).1 (Finset.mem_product.mp hzj).1

theorem IsPartition.product_right {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {L : Nat} {Q : Fin L → Finset Y} {T : Finset Y} (hQ : IsPartition Q T)
    (S : Finset X) : IsPartition (fun j => S.product (Q j)) (S.product T) := by
  constructor
  · intro z
    rcases z with ⟨x, y⟩
    constructor
    · intro hz
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hz
      obtain ⟨j, hj⟩ := (hQ.1 y).mp hy
      exact ⟨j, Finset.mem_product.mpr ⟨hx, hj⟩⟩
    · rintro ⟨j, hz⟩
      obtain ⟨hx, hj⟩ := Finset.mem_product.mp hz
      exact Finset.mem_product.mpr ⟨hx, (hQ.1 y).mpr ⟨j, hj⟩⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro z hzi hzj
    exact Finset.disjoint_left.mp (hQ.2 i j hij)
      (Finset.mem_product.mp hzi).2 (Finset.mem_product.mp hzj).2

theorem product_partition_inter_sum_card {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {M L : Nat} (P : Fin M → Finset X) (Q : Fin L → Finset Y) (S : Finset X) (T : Finset Y)
    (hP : IsPartition P S) (hQ : IsPartition Q T) (B : Finset (X × Y)) (hB : B ⊆ S.product T) :
    (∑ i, ∑ j, ((P i).product (Q j) ∩ B).card) = B.card := by
  classical
  let A : Fin M → Finset (X × Y) := fun i => (P i).product T ∩ B
  have hA : IsPartition A B := (hP.product_left T).inter_subset B hB
  have hinner (i : Fin M) : (∑ j, ((P i).product (Q j) ∩ B).card) = (A i).card := by
    have hpart := (hQ.product_right (P i)).inter_subset (A i) Finset.inter_subset_left
    have hcells (j : Fin L) : (P i).product (Q j) ∩ A i = (P i).product (Q j) ∩ B := by
      ext z
      constructor
      · intro hz
        have h1 := Finset.mem_inter.mp hz
        have h2 := Finset.mem_inter.mp h1.2
        exact Finset.mem_inter.mpr ⟨h1.1, h2.2⟩
      · intro hz
        obtain ⟨hpq, hzB⟩ := Finset.mem_inter.mp hz
        obtain ⟨hx, hy⟩ := Finset.mem_product.mp hpq
        have hzA : z ∈ A i := Finset.mem_inter.mpr
          ⟨Finset.mem_product.mpr ⟨hx, (hQ.cell_subset j) hy⟩, hzB⟩
        exact Finset.mem_inter.mpr ⟨hpq, hzA⟩
    simpa only [hcells] using hpart.sum_card
  calc
    _ = ∑ i, (A i).card := Finset.sum_congr rfl (fun i _ => hinner i)
    _ = B.card := hA.sum_card

end LeanProofs.GowersSzemeredi
