import GowersSzemeredi.Proofs07UniversalPartition
import GowersSzemeredi.Proofs13PartitionSelection

/-! The coefficient partition and weighted selection used by Lemma 13.9.
The two coefficient maps share one domain and therefore one spectrum.

`extract_bilinear_cell`, `lemma_13_9_of_length_comparison`,
`lemma_13_9_of_progression_length_bound` and `stage139_height_card_lower` are in
`Proofs13CoefficientPartitionSide`, outside the final route. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Pulling a partition back through a coordinate partitions the original
finite set, provided that coordinate lies in the partitioned domain. -/
theorem coordinate_filter_partition {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {q : Nat} (C : Finset X) (R : Finset Y) (f : X → Y) (P : Fin q → Finset Y)
    (hP : IsPartition P R) (hC : ∀ z ∈ C, f z ∈ R) :
    IsPartition (fun j ↦ C.filter fun z ↦ f z ∈ P j) C := by
  constructor
  · intro z
    constructor
    · intro hz
      obtain ⟨j, hj⟩ := (hP.1 (f z)).mp (hC z hz)
      exact ⟨j, Finset.mem_filter.mpr ⟨hz, hj⟩⟩
    · rintro ⟨j, hj⟩
      exact (Finset.mem_filter.mp hj).1
  · intro i j hij
    rw [Finset.disjoint_left]
    intro z hi hj
    exact Finset.disjoint_left.mp (hP.2 i j hij)
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

/-- Weighted averaging retains mass per coordinate on one partition cell. -/
theorem exists_coordinate_filter_cell {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    {q : Nat} (C : Finset X) (R : Finset Y) (f : X → Y) (P : Fin q → Finset Y)
    (hR : R.Nonempty) (hP : IsPartition P R) (hC : ∀ z ∈ C, f z ∈ R)
    {b : Real} (hmass : b * R.card ≤ C.card) :
    ∃ j : Fin q, b * (P j).card ≤ (C.filter fun z ↦ f z ∈ P j).card := by
  obtain ⟨x, hx⟩ := hR
  obtain ⟨j, _⟩ := (hP.1 x).mp hx
  letI : Nonempty (Fin q) := ⟨j⟩
  have hs : (∑ j, b * ((P j).card : Real)) ≤
      ∑ j, ((C.filter fun z ↦ f z ∈ P j).card : Real) := by
    rw [← Finset.mul_sum, ← Nat.cast_sum, hP.sum_card,
      ← Nat.cast_sum, (coordinate_filter_partition C R f P hP hC).sum_card]
    exact hmass
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hs
  exact ⟨j, hj⟩

/-- A row-supported set has at most the product of the column and height
cardinalities, including after translating all heights. -/
theorem translated_row_card_le {N : Nat} (C : Finset (Pair N))
    (S J : Finset (ZMod N)) (y : ZMod N)
    (hsupport : ∀ z ∈ C, z.1 ∈ S ∧ z.2 - y ∈ J) :
    C.card ≤ S.card * J.card := by
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun z : Pair N ↦ (z.1, z.2 - y))
  · intro z hz
    exact Finset.mem_product.mpr (hsupport z hz)
  · intro z _ w _ hzw
    change (z.1, z.2 - y) = (w.1, w.2 - y) at hzw
    obtain ⟨hx, hy⟩ := Prod.mk.inj hzw
    exact Prod.ext hx (by simpa using congrArg (fun t : ZMod N ↦ t + y) hy)

/-- Affine variation of both row coefficients gives a bilinear formula in
the original two coordinates, with the height translation accounted for. -/
theorem bilinearOn_of_affine_row_coefficients {N : Nat}
    (C : Finset (Pair N)) (J : Finset (ZMod N)) (y : ZMod N)
    (phi : Pair N → ZMod N) (a c : ZMod N → ZMod N)
    (hsupport : ∀ z ∈ C, z.2 - y ∈ J)
    (hrow : ∀ z ∈ C, phi z = a (z.2 - y) + c (z.2 - y) * z.1)
    (ha : LinearOn J a) (hc : LinearOn J c) : BilinearOn C phi := by
  obtain ⟨aa, ab, ha⟩ := ha
  obtain ⟨ca, cb, hc⟩ := hc
  let mu : Pair N → ZMod N := fun z ↦
    (ab - aa * y) + (cb - ca * y) * z.1 + aa * z.2 + ca * z.1 * z.2
  refine ⟨mu, ⟨ab - aa * y, cb - ca * y, aa, ca, fun _ ↦ rfl⟩, ?_⟩
  intro z hz
  rw [hrow z hz, ha _ (hsupport z hz), hc _ (hsupport z hz)]
  dsimp only [mu]
  ring

set_option exponentiation.threshold 512 in
/-- The corrected Stage 13.8 density yields the precise Stage 13.9 exponent,
without a factor-two loss for the two coefficient maps. -/
theorem stage139_partition_exponent (alpha : Real) :
    cor711Exponent ((2 : Real) ^ (-(135 : Int)) * alpha ^ 704) 1 =
      (2 : Real) ^ (-(284 : Int)) * alpha ^ 1408 := by
  unfold cor711Exponent
  norm_num [Real.rpow_neg, zpow_neg]
  ring

end LeanProofs.GowersSzemeredi
