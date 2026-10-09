import GowersSzemeredi.Proofs16BoundedBadRelations

/-! Outside the bad-relation sets, the exact single and paired splitting
identities hold. Few bad pairs also force few bad individual vertices. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def boundedRelationClass {N : Nat} [Fact N.Prime] {κ : Type*} [Fintype κ]
    (D : Finset (ZMod N)) (L : κ → ZMod N → ZMod N) (R : Nat) :
    Set (κ → centeredBall N R) :=
  {w | (fun j => (w j : ZMod N)) ∈ relationSubmodule D L}

theorem relation_sum_eq_zero {N : Nat} [Fact N.Prime] {κ : Type*} [Fintype κ]
    (D : Finset (ZMod N)) (L : κ → ZMod N → ZMod N) (hzero : ∀ j, L j 0 = 0)
    {w : κ → ZMod N} (hw : w ∈ relationSubmodule D L) {x : ZMod N} (hx : x ∈ D) :
    ∑ j, w j * L j x = 0 := by
  simpa only [hzero, sub_zero] using hw x hx

/-- A good pair has exactly the split bounded relations. -/
theorem bounded_pair_split_of_not_bad {N : Nat} [NeZero N] [Fact N.Prime]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (gamma : ι → ZMod N)
    (D : Finset (ZMod N)) (L : κ → ZMod N → ZMod N) (hzero : ∀ j, L j 0 = 0)
    (C : Finset (ZMod N)) (hC : C ⊆ D) (R : Nat)
    {x y : ZMod N} (hx : x ∈ C) (hy : y ∈ C)
    (hgood : (x, y) ∉ boundedBadRelationPairs gamma D L C R)
    (nu : ι → centeredBall N R) (w v : κ → centeredBall N R) :
    (∑ i, (nu i : ZMod N) * gamma i) + (∑ j, (w j : ZMod N) * L j x) +
        (∑ j, (v j : ZMod N) * L j y) = 0 ↔
      (∑ i, (nu i : ZMod N) * gamma i = 0 ∧
        w ∈ boundedRelationClass D L R ∧ v ∈ boundedRelationClass D L R) := by
  constructor
  · intro hrel
    have hbad : ¬ ((fun j => (w j : ZMod N)) ∉ relationSubmodule D L ∨
        (fun j => (v j : ZMod N)) ∉ relationSubmodule D L) := by
      intro h
      exact hgood (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, nu, w, v, h, hrel⟩)
    push Not at hbad
    have hw := relation_sum_eq_zero D L hzero hbad.1 (hC hx)
    have hv := relation_sum_eq_zero D L hzero hbad.2 (hC hy)
    refine ⟨?_, hbad.1, hbad.2⟩
    simpa only [hw, hv, add_zero] using hrel
  · rintro ⟨hnu, hw, hv⟩
    rw [hnu, relation_sum_eq_zero D L hzero hw (hC hx),
      relation_sum_eq_zero D L hzero hv (hC hy)]
    simp

/-- The sum-indexed form consumed by the paired Bohr factorization. -/
theorem bounded_pair_sum_split_of_not_bad {N : Nat} [NeZero N] [Fact N.Prime]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (gamma : ι → ZMod N)
    (D : Finset (ZMod N)) (L : κ → ZMod N → ZMod N) (hzero : ∀ j, L j 0 = 0)
    (C : Finset (ZMod N)) (hC : C ⊆ D) (R : Nat)
    {x y : ZMod N} (hx : x ∈ C) (hy : y ∈ C)
    (hgood : (x, y) ∉ boundedBadRelationPairs gamma D L C R)
    (nu : ι → centeredBall N R) (mu : (κ ⊕ κ) → centeredBall N R) :
    (∑ i, (nu i : ZMod N) * gamma i) +
      (∑ j, (mu j : ZMod N) * Sum.elim (fun k => L k x) (fun k => L k y) j) = 0 ↔
      (∑ i, (nu i : ZMod N) * gamma i = 0 ∧
        (fun j => mu (Sum.inl j)) ∈ boundedRelationClass D L R ∧
        (fun j => mu (Sum.inr j)) ∈ boundedRelationClass D L R) := by
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, add_assoc] using
    bounded_pair_split_of_not_bad gamma D L hzero C hC R hx hy hgood nu
      (fun j => mu (Sum.inl j)) (fun j => mu (Sum.inr j))

def boundedBadRelationVertices {N : Nat} [NeZero N] [Fact N.Prime]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (gamma : ι → ZMod N)
    (D : Finset (ZMod N)) (L : κ → ZMod N → ZMod N) (C : Finset (ZMod N)) (R : Nat) :
    Finset (ZMod N) := C.filter fun x => ∃ (nu : ι → centeredBall N R) (w : κ → centeredBall N R),
      (fun j => (w j : ZMod N)) ∉ relationSubmodule D L ∧
        (∑ i, (nu i : ZMod N) * gamma i) + (∑ j, (w j : ZMod N) * L j x) = 0

/-- A bad vertex makes every pair with it bad, by taking zero coefficients
on the second vertex. -/
theorem bad_relation_vertex_product_subset {N : Nat} [NeZero N] [Fact N.Prime]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (gamma : ι → ZMod N)
    (D : Finset (ZMod N)) (L : κ → ZMod N → ZMod N) (C : Finset (ZMod N)) (R : Nat) :
    (boundedBadRelationVertices gamma D L C R) ×ˢ C ⊆ boundedBadRelationPairs gamma D L C R := by
  intro p hp
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
  obtain ⟨hxC, nu, w, hbad, hrel⟩ := Finset.mem_filter.mp hx
  have hz : (0 : ZMod N) ∈ centeredBall N R := by simp [centeredBall, centeredAbs]
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hxC, hy⟩,
    nu, w, (fun _ => ⟨0, hz⟩), Or.inl hbad, ?_⟩
  simpa using hrel

/-- Controlling the bad-pair fraction automatically controls bad vertices. -/
theorem bad_relation_vertices_card_le {N : Nat} [NeZero N] [Fact N.Prime]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (gamma : ι → ZMod N)
    (D : Finset (ZMod N)) (L : κ → ZMod N → ZMod N) (C : Finset (ZMod N))
    (hC : C.Nonempty) (R : Nat) {theta : Real}
    (hbad : ((boundedBadRelationPairs gamma D L C R).card : Real) ≤ theta * (C.card : Real)^2) :
    ((boundedBadRelationVertices gamma D L C R).card : Real) ≤ theta * C.card := by
  have hc : (0 : Real) < C.card := by exact_mod_cast hC.card_pos
  have hcard : ((boundedBadRelationVertices gamma D L C R).card : Real) * C.card ≤
      (boundedBadRelationPairs gamma D L C R).card := by
    exact_mod_cast (show (boundedBadRelationVertices gamma D L C R).card * C.card ≤ _ by
      rw [← Finset.card_product]
      exact Finset.card_le_card (bad_relation_vertex_product_subset gamma D L C R))
  apply (mul_le_mul_iff_left₀ hc).mp
  nlinarith only [hcard, hbad]

/-- A good individual vertex has the single-block splitting identity. -/
theorem bounded_single_split_of_not_bad {N : Nat} [NeZero N] [Fact N.Prime]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (gamma : ι → ZMod N)
    (D : Finset (ZMod N)) (L : κ → ZMod N → ZMod N) (hzero : ∀ j, L j 0 = 0)
    (C : Finset (ZMod N)) (hC : C ⊆ D) (R : Nat) {x : ZMod N} (hx : x ∈ C)
    (hgood : x ∉ boundedBadRelationVertices gamma D L C R)
    (nu : ι → centeredBall N R) (w : κ → centeredBall N R) :
    (∑ i, (nu i : ZMod N) * gamma i) + (∑ j, (w j : ZMod N) * L j x) = 0 ↔
      (∑ i, (nu i : ZMod N) * gamma i = 0 ∧ w ∈ boundedRelationClass D L R) := by
  constructor
  · intro hrel
    have hw : (fun j => (w j : ZMod N)) ∈ relationSubmodule D L := by
      by_contra h
      exact hgood (Finset.mem_filter.mpr ⟨hx, nu, w, h, hrel⟩)
    refine ⟨?_, hw⟩
    simpa only [relation_sum_eq_zero D L hzero hw (hC hx), add_zero] using hrel
  · rintro ⟨hnu, hw⟩
    rw [hnu, relation_sum_eq_zero D L hzero hw (hC hx), add_zero]

end LeanProofs.GowersSzemeredi
