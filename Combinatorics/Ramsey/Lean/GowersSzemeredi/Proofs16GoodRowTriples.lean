import GowersSzemeredi.Proofs16IndexPatternAveraging

/-! Count four-row configurations by the second moment of difference
fibers, and retain their density after removing exceptional triples. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def rowPairOffsets {N : Nat} [NeZero N] (Y : Finset (ZMod N)) (y : ZMod N) : Finset (ZMod N) :=
  Finset.univ.filter fun z => y + z ∈ Y ∧ z ∈ Y

def rowQuadrupleTriples {N : Nat} [NeZero N] (Y : Finset (ZMod N)) : Finset (ZMod N × ZMod N × ZMod N) :=
  Finset.univ.filter fun t => t.1 + t.2.1 ∈ Y ∧ t.2.1 ∈ Y ∧ t.1 + t.2.2 ∈ Y ∧ t.2.2 ∈ Y

theorem rowPairOffsets_card {N : Nat} [NeZero N] (Y : Finset (ZMod N)) (y : ZMod N) :
    (rowPairOffsets Y y).card = ((Y ×ˢ Y).filter fun p => p.1 - p.2 = y).card := by
  apply Finset.card_bij (fun z _ => (y + z, z))
  · intro z hz
    obtain ⟨_, h1, h2⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, h2⟩, by simp⟩
  · intro z hz w hw h
    exact congrArg Prod.snd h
  · intro p hp
    obtain ⟨hp, heq⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    have hsum : y + p.2 = p.1 := by rw [← heq]; ring
    exact ⟨p.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hsum] using ha, hb⟩,
      Prod.ext hsum rfl⟩

theorem rowPairOffsets_sum {N : Nat} [NeZero N] (Y : Finset (ZMod N)) :
    (∑ y : ZMod N, (rowPairOffsets Y y).card) = Y.card^2 := by
  simp_rw [rowPairOffsets_card]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp [pow_two]

theorem rowQuadrupleTriples_card {N : Nat} [NeZero N] (Y : Finset (ZMod N)) :
    (rowQuadrupleTriples Y).card = ∑ y : ZMod N, (rowPairOffsets Y y).card^2 := by
  have hsum := Finset.sum_card_fiberwise_eq_card_filter (rowQuadrupleTriples Y)
    (Finset.univ : Finset (ZMod N)) Prod.fst
  simp only [Finset.mem_univ, Finset.filter_true] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro y hy
  have hbij : ((rowQuadrupleTriples Y).filter fun t => t.1 = y).card =
      (rowPairOffsets Y y ×ˢ rowPairOffsets Y y).card := by
    apply Finset.card_bij (fun t _ => t.2)
    · intro t ht
      have hty := (Finset.mem_filter.mp ht).2
      have hmem := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2
      change t.1 + t.2.1 ∈ Y ∧ t.2.1 ∈ Y ∧ t.1 + t.2.2 ∈ Y ∧ t.2.2 ∈ Y at hmem
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        by simpa only [hty] using hmem.1, hmem.2.1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [hty] using hmem.2.2.1, hmem.2.2.2⟩⟩
    · intro t ht u hu heq
      exact Prod.ext ((Finset.mem_filter.mp ht).2.trans (Finset.mem_filter.mp hu).2.symm) heq
    · intro p hp
      obtain ⟨hz, hw⟩ := Finset.mem_product.mp hp
      obtain ⟨_, hz1, hz2⟩ := Finset.mem_filter.mp hz
      obtain ⟨_, hw1, hw2⟩ := Finset.mem_filter.mp hw
      exact ⟨(y, p), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hz1, hz2, hw1, hw2⟩, rfl⟩, rfl⟩
  simpa only [Finset.card_product, pow_two] using hbij

/-- Cauchy-Schwarz gives at least |Y|^4/N admissible triples. -/
theorem rowQuadrupleTriples_card_lower {N : Nat} [NeZero N] (Y : Finset (ZMod N)) :
    Y.card^4 ≤ N * (rowQuadrupleTriples Y).card := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (R := Nat) Finset.univ
    (fun _ : ZMod N => 1) (fun y => (rowPairOffsets Y y).card)
  simpa [rowPairOffsets_sum, ← rowQuadrupleTriples_card, ← pow_mul] using h

/-- Removing epsilon*N^3 exceptional triples costs exactly epsilon in
the fourth-power density lower bound. -/
theorem good_row_triples_density {N : Nat} [NeZero N]
    (Y : Finset (ZMod N)) (B : Finset (ZMod N × ZMod N × ZMod N))
    {beta epsilon : Real} (hbeta : 0 ≤ beta) (hY : beta * N ≤ Y.card)
    (hB : (B.card : Real) ≤ epsilon * (N : Real)^3) :
    (beta^4 - epsilon) * (N : Real)^3 ≤ ((rowQuadrupleTriples Y \ B).card : Real) := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hcount : ((rowQuadrupleTriples Y).card : Real) ≤
      (rowQuadrupleTriples Y \ B).card + B.card := by
    exact_mod_cast Finset.card_le_card_sdiff_add_card (s := rowQuadrupleTriples Y) (t := B)
  have hlower : (Y.card : Real)^4 ≤ N * (rowQuadrupleTriples Y).card := by
    exact_mod_cast rowQuadrupleTriples_card_lower Y
  have hp := pow_le_pow_left₀ (mul_nonneg hbeta hN.le) hY 4
  have hc := mul_le_mul_of_nonneg_left hcount hN.le
  have hb := mul_le_mul_of_nonneg_left hB hN.le
  apply (mul_le_mul_iff_right₀ hN).mp
  nlinarith only [hp, hlower, hc, hb]

/-- The good four-row configurations yield fixed small index patterns and
fixed offsets with an explicit density loss. -/
theorem exists_dense_fixed_index_patterns {N m ell : Nat} [NeZero N]
    (Y : Finset (ZMod N)) (B : Finset (ZMod N × ZMod N × ZMod N))
    (I : ZMod N → Finset (Fin m)) (hI : ∀ y, (I y).card ≤ ell)
    {beta epsilon : Real} (hbeta : 0 ≤ beta) (hY : beta * N ≤ Y.card)
    (hB : (B.card : Real) ≤ epsilon * (N : Real)^3) :
    ∃ (J : Fin 4 → Finset (Fin m)) (z w : ZMod N) (V : Finset (ZMod N)),
      (∀ i, (J i).card ≤ ell) ∧
      (beta^4 - epsilon) * N ≤ ((m + 1 : Nat)^(4 * ell) : Real) * V.card ∧
      ∀ y ∈ V, (y, z, w) ∈ rowQuadrupleTriples Y \ B ∧
        I (y + z) = J 0 ∧ I z = J 1 ∧ I (y + w) = J 2 ∧ I w = J 3 := by
  obtain ⟨J, z, w, V, hJ, hcount, hV⟩ := exists_fixed_index_patterns (rowQuadrupleTriples Y \ B) I hI
  refine ⟨J, z, w, V, hJ, ?_, hV⟩
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hc : ((rowQuadrupleTriples Y \ B).card : Real) ≤
      ((m + 1 : Nat)^(4 * ell) : Real) * (N : Real)^2 * V.card := by exact_mod_cast hcount
  have hg := good_row_triples_density Y B hbeta hY hB
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hN)).mp
  nlinarith only [hg, hc]

end LeanProofs.GowersSzemeredi
