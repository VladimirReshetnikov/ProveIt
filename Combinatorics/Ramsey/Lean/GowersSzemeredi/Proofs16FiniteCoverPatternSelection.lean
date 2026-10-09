import GowersSzemeredi.Proofs16PairFrequencyEightCover

/-! Select one cell from each of finitely many covers while retaining
whole configurations. The loss depends on the cover counts, not the size
of the ambient configuration space. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exists_dense_cover_pattern {X Y I : Type*} [Fintype I]
    (Q : Finset X) (C : I → Finset (Finset Y)) (f : X → I → Y) {M : Nat}
    (hQ : Q.Nonempty) (hC : ∀ i, (C i).Nonempty) (hcount : ∀ i, (C i).card ≤ M)
    (hcover : ∀ q ∈ Q, ∀ i, ∃ D ∈ C i, f q i ∈ D) :
    ∃ (D : I → Finset Y) (R : Finset X), (∀ i, D i ∈ C i) ∧ R ⊆ Q ∧
      Q.card ≤ M^(Fintype.card I)*R.card ∧ R.Nonempty ∧ ∀ q ∈ R, ∀ i, f q i ∈ D i := by
  have hselect (q : X) (i : I) : ∃ c : ↥(C i), q ∈ Q → f q i ∈ (c : Finset Y) := by
    by_cases hq : q ∈ Q
    · obtain ⟨D,hD,hf⟩ := hcover q hq i
      exact ⟨⟨D,hD⟩,fun _ => hf⟩
    · obtain ⟨D,hD⟩ := hC i
      exact ⟨⟨D,hD⟩,fun h => (hq h).elim⟩
  choose code hcode using hselect
  obtain ⟨q0,hq0⟩ := hQ
  letI : Nonempty (∀ i, ↥(C i)) := ⟨code q0⟩
  have hsum : (∑ c : ∀ i, ↥(C i), (Q.filter fun q => code q = c).card) = Q.card := by
    simpa only [Finset.mem_univ,Finset.filter_true] using
      Finset.sum_card_fiberwise_eq_card_filter Q Finset.univ code
  have hle : (∑ _c : ∀ i, ↥(C i), Q.card) ≤
      ∑ c : ∀ i, ↥(C i), Fintype.card (∀ i, ↥(C i))*(Q.filter fun q => code q = c).card := by
    rw [← Finset.mul_sum,hsum]
    simp
  obtain ⟨c,_,hc⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hle
  let R := Q.filter fun q => code q = c
  have hcard : Fintype.card (∀ i, ↥(C i)) ≤ M^(Fintype.card I) := by
    rw [Fintype.card_pi]
    calc (∏ i, Fintype.card ↥(C i)) = ∏ i, (C i).card := by simp only [Fintype.card_coe]
      _ ≤ ∏ _i : I, M := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hcount i)
      _ = _ := by simp
  have hmass : Q.card ≤ M^(Fintype.card I)*R.card :=
    hc.trans (Nat.mul_le_mul_right R.card hcard)
  have hR : R.Nonempty := by
    apply Finset.card_pos.mp
    have hq := Finset.card_pos.mpr (show Q.Nonempty from ⟨q0,hq0⟩)
    by_contra hn
    have he : R.card = 0 := by omega
    simp only [he,Nat.mul_zero] at hmass
    omega
  refine ⟨fun i => (c i : Finset Y),R,fun i => (c i).property,Finset.filter_subset _ _,hmass,hR,?_⟩
  intro q hq i
  obtain ⟨hq,hqc⟩ := Finset.mem_filter.mp hq
  have h := hcode q i hq
  rw [hqc] at h
  exact h

end LeanProofs.GowersSzemeredi
