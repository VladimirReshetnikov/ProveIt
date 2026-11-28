import GRHArticle.ProgressionFree.IntervalRothMask

/-!
# Eight-position bounds for the finite interval search

The table packs 256 upper bounds into three bits per entry. Its individual
entries are checked by the basic interval search. Partitioning the
remaining positions into eight-position intervals gives a stronger bound
at every node of the larger computations.
-/

namespace GRHArticle.ProgressionFree

open Finset

private def byteRothBound (r : ℕ) : ℕ :=
  let table := 887153195600046588399356313217589510950724417620616821946678964596692103420443287290956043588734786066990415444263530858758843350309421837610759425242908988733890425977264232370627856738577641139054907631093914023535032655713735752
  (table >>> (3*(r%256))) % 8

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
private theorem byteRothTable_sound : ∀ i : Fin 256,
    intervalMaskCheck (byteRothBound i) 8 0 0 i 0 = true := by decide +kernel

private def byteBudget : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k+1, r => if r=0 then 0 else byteRothBound (r%256) + byteBudget k (r >>> 8)

private theorem card_le_byteBudget (k r : ℕ) (S : Finset ℕ) (hS : S ⊆ range (8*k))
    (hf : ThreeAPFree (S : Set ℕ)) (hr : ∀ j ∈ S, r.testBit j = true) : S.card ≤ byteBudget k r := by
  induction k generalizing r S with
  | zero =>
    have : S = ∅ := by simpa using hS
    simp [this,byteBudget]
  | succ k ih =>
    rw [byteBudget]
    by_cases h0 : r=0
    · subst r
      have he : S = ∅ := eq_empty_iff_forall_notMem.mpr (fun x hx ↦ by simpa using hr x hx)
      simp [he]
    rw [if_neg h0]
    let L := S.filter (· < 8)
    let H := (range (8*k)).filter (fun j ↦ 8+j ∈ S)
    let i : Fin 256 := ⟨r%256,Nat.mod_lt _ (by decide)⟩
    have hL : L.card ≤ byteRothBound (r%256) := by
      have hm := intervalMaskCheck_sound (byteRothTable_sound i) (hf.mono (filter_subset ..))
        (B := L) (fun _ hj ↦ mem_range.mpr (mem_filter.mp hj).2) (by
          intro j hj
          obtain ⟨hm,hn⟩ := mem_filter.mp hj
          change (r % 2^8).testBit j = true
          rw [Nat.testBit_mod_two_pow r 8 j]
          simp [hn,hr j hm])
      simpa [i] using hm
    have hH : H.card ≤ byteBudget k (r >>> 8) := by
      apply ih _ H (filter_subset ..)
      · intro a ha b hb c hc he
        exact Nat.add_left_cancel (hf (mem_filter.mp ha).2 (mem_filter.mp hb).2 (mem_filter.mp hc).2
          (show (8+a)+(8+c)=(8+b)+(8+b) by omega))
      · intro j hj
        rw [Nat.testBit_shiftRight]
        exact hr _ (mem_filter.mp hj).2
    have he : (S.filter (fun j ↦ ¬ j < 8)).card ≤ H.card := by
      apply card_le_card_of_injOn (fun j ↦ j-8)
      · intro j hj
        obtain ⟨hm,hn⟩ := mem_filter.mp hj
        have ht := mem_range.mp (hS hm)
        change j-8 ∈ H
        apply mem_filter.mpr
        exact ⟨mem_range.mpr (by omega), by rwa [show 8+(j-8) = j by omega]⟩
      · intro a ha b hb he
        have ha' : ¬ a < 8 := (mem_filter.mp ha).2
        have hb' : ¬ b < 8 := (mem_filter.mp hb).2
        change a-8=b-8 at he
        omega
    have hcard := card_filter_add_card_filter_not (s := S) (fun j ↦ j < 8)
    change L.card + _ = S.card at hcard
    omega

private def maskByteCapacity (n r b : ℕ) : ℕ :=
  byteBudget n r + byteBudget n (r &&& b)

/-- The larger interval search prunes using certified eight-position bounds. -/
def intervalByteCheck (M n r b : ℕ) : Bool := intervalMaskCheckWith maskByteCapacity M n 0 0 r b

private theorem chosenMass_le_byteCapacity (B : Finset ℕ) (hf : ThreeAPFree (B : Set ℕ))
    (y n r b : ℕ) (hr : IntervalMaskAvailable B y n r) :
    intervalChosenMass B y n b ≤ maskByteCapacity n r b := by
  let S := (range n).filter (fun j ↦ y+j ∈ B)
  let T := S.filter (fun j ↦ b.testBit j = true)
  have hS (j : ℕ) (hj : j ∈ S) : j < n ∧ y+j ∈ B :=
    ⟨mem_range.mp (mem_filter.mp hj).1,(mem_filter.mp hj).2⟩
  have hu : S ⊆ range (8*n) := fun j hj ↦ mem_range.mpr (by have := (hS j hj).1; omega)
  have hfree : ThreeAPFree (S : Set ℕ) := by
    intro a ha c hc d hd he
    exact Nat.add_left_cancel (hf (hS a ha).2 (hS c hc).2 (hS d hd).2
      (show (y+a)+(y+d)=(y+c)+(y+c) by omega))
  have hb := card_le_byteBudget n r S hu hfree (fun j hj ↦ hr j (hS j hj).1 (hS j hj).2)
  have ht := card_le_byteBudget n (r &&& b) T (fun _ hj ↦ hu (mem_filter.mp hj).1)
    (hfree.mono (filter_subset ..)) (by
      intro j hj
      obtain ⟨hj,hbit⟩ := mem_filter.mp hj
      simp [Nat.testBit_and, hr j (hS j hj).1 (hS j hj).2,hbit])
  have he : intervalChosenMass B y n b = S.card + T.card := by
    unfold intervalChosenMass
    rw [← sum_filter]
    change (∑ j ∈ S, (1+(b.testBit j).toNat)) = _
    rw [sum_add_distrib]
    simp only [sum_const,nsmul_eq_mul,mul_one]
    congr 1
    change (∑ j ∈ S, (b.testBit j).toNat) = _
    calc
      _ = ∑ j ∈ S, if b.testBit j = true then 1 else 0 :=
        sum_congr rfl fun j _ ↦ by cases b.testBit j <;> rfl
      _ = _ := by rw [sum_boole]; rfl
  rw [he]
  exact Nat.add_le_add hb ht

theorem intervalByteCheck_sound {n M r b : ℕ} (hc : intervalByteCheck M n r b = true)
    {B : Finset ℕ} (hf : ThreeAPFree (B : Set ℕ)) (hB : B ⊆ range n)
    (hr : ∀ j ∈ B, r.testBit j = true) : ∑ j ∈ B, (1+(b.testBit j).toNat) ≤ M :=
  intervalMaskCheckWith_sound _ hc hf hB hr (chosenMass_le_byteCapacity B hf)

end GRHArticle.ProgressionFree
