import GowersSzemeredi.Proofs16OrientedPairs

/-! Symmetric dense column-pair graphs with coherent difference fibres. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem ColumnPairIdentity.swap {N : Nat} [NeZero N]
    {T : ZMod N → Finset (ZMod N)} {L : ZMod N → ZMod N → ZMod N}
    {r : Real} {p q : ZMod N × ZMod N} (h : ColumnPairIdentity T L r p q) :
    ColumnPairIdentity T L r p.swap q.swap := by
  intro y hp2 hp1 hq2 hq1
  have heq := h y hp1 hp2 hq1 hq2
  change L p.2 y-L p.1 y = L q.2 y-L q.1 y
  linear_combination -heq

theorem ColumnPairIdentity.of_zero_difference {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (r : Real) {p q : ZMod N × ZMod N} (hp : p.1-p.2 = 0) (hq : q.1-q.2 = 0) :
    ColumnPairIdentity T L r p q := by
  intro y _ _ _ _
  simp only [sub_eq_zero.mp hp, sub_eq_zero.mp hq, sub_self]

/-- Symmetrize coherent pairs while retaining at least half their
cardinality. Mixed orientations meet only in the diagonal fibre. -/
theorem exists_symmetric_coherent_pairs {N : Nat} [NeZero N] [Fact N.Prime]
    (hN : 2 < N) (X : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N) (r : Real)
    (P : Finset (ZMod N × ZMod N)) (hPX : P ⊆ X ×ˢ X)
    (hcoh : ∀ p ∈ P, ∀ q ∈ P, p.1-p.2 = q.1-q.2 → ColumnPairIdentity T L r p q) :
    ∃ Q : Finset (ZMod N × ZMod N), P.card ≤ 2 * Q.card ∧ Q ⊆ X ×ˢ X ∧
      (∀ p ∈ Q, p.swap ∈ Q) ∧
      (∀ p ∈ Q, ∀ q ∈ Q, p.1-p.2 = q.1-q.2 → ColumnPairIdentity T L r p q) := by
  obtain ⟨S, hSP, hsize, horient⟩ := exists_oriented_pair_subset P
  let Q := S ∪ S.image Prod.swap
  have hSQ : S ⊆ Q := Finset.subset_union_left
  have hzero : ∀ p ∈ S, ∀ q ∈ S, p.1-p.2 = -(q.1-q.2) → p.1-p.2 = 0 := by
    intro p hp q hq hd
    exact prime_self_opposite_zero hN (horient p hp q hq hd)
  have hmixed : ∀ p ∈ S, ∀ q ∈ S, p.1-p.2 = q.2-q.1 →
      ColumnPairIdentity T L r p q.swap := by
    intro p hp q hq hd
    have hp0 := hzero p hp q hq (by linear_combination hd)
    exact ColumnPairIdentity.of_zero_difference T L r hp0 (hd.symm.trans hp0)
  refine ⟨Q, hsize.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card hSQ)), ?_, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hPX (hSP hp)
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      have hqX := Finset.mem_product.mp (hPX (hSP hq))
      exact Finset.mem_product.mpr ⟨hqX.2, hqX.1⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_union_left _ hq
  · intro p hp q hq hd
    rcases Finset.mem_union.mp hp with hp | hp <;> rcases Finset.mem_union.mp hq with hq | hq
    · exact hcoh p (hSP hp) q (hSP hq) hd
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
      exact hmixed p hp z hz hd
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
      exact (hmixed q hq z hz hd.symm).symm
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
      exact (hcoh z (hSP hz) w (hSP hw) (by
        change z.2-z.1 = w.2-w.1 at hd
        linear_combination -hd)).swap

end LeanProofs.GowersSzemeredi
