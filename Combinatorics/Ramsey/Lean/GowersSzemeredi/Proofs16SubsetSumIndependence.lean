import GowersSzemeredi.Proofs16SpanBallSplit

/-! `{-1,0,1}`-independence for the iteration of Milićević's Proposition 9.3
(arXiv:2601.01682, printed pp. 65–66).

A finite set `V` of frequencies is `{-1,0,1}`-independent exactly when its
`{0,1}`-subset sums are distinct (`SubsetSumInjective`). Each round of the
iteration adjoins one new frequency `Θ(a)` to the set `{θ_i(a) : i ∈ I}`,
and Claim 9.4 guarantees that `Θ(a)` avoids the `{-1,0,1}`-span.
* `sub_sum_mem_spanBall_one`: for `A, B ⊆ V`, `∑B − ∑A ∈ ⟨V⟩_1`.
* `subsetSumInjective_insert`: adjoining `w ∉ ⟨V⟩_1` keeps subset sums
  distinct.
* `card_le_of_subsetSumInjective`: inside `⟨Γ⟩_R`, an independent set has
  `2^|V| ≤ (2|V|R + 1)^|Γ|`, Milićević's cap `|I_{x,y}| ≤ s₀`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Distinct `{0,1}`-subset sums, i.e. `{-1,0,1}`-independence. -/
def SubsetSumInjective {G : Type*} [AddCommGroup G] (V : Finset G) : Prop :=
  ∀ A ⊆ V, ∀ B ⊆ V, ∑ v ∈ A, v = ∑ v ∈ B, v → A = B

theorem sub_sum_mem_spanBall_one {G : Type*} [AddCommGroup G] {V A B : Finset G}
    (hA : A ⊆ V) (hB : B ⊆ V) : ∑ v ∈ B, v - ∑ v ∈ A, v ∈ spanBall V 1 := by
  refine (mem_spanBall_iff V 1 _).mpr
    ⟨fun v => (if v ∈ B then 1 else 0) - (if v ∈ A then 1 else 0), fun v _ => ?_, ?_⟩
  · show -((1 : Nat) : Int) ≤ (if v ∈ B then 1 else 0) - (if v ∈ A then 1 else 0) ∧
      (if v ∈ B then 1 else 0) - (if v ∈ A then 1 else 0) ≤ ((1 : Nat) : Int)
    split_ifs <;> simp
  · have e : ∀ C ⊆ V, ∑ v ∈ V, (if v ∈ C then (1 : Int) else 0) • v = ∑ v ∈ C, v := by
      intro C hC
      simp_rw [ite_smul, one_smul, zero_smul]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hC]
    rw [← e B hB, ← e A hA, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [sub_smul]

theorem self_mem_spanBall_one {G : Type*} [AddCommGroup G] {V : Finset G} {w : G}
    (hw : w ∈ V) : w ∈ spanBall V 1 := by
  have h := sub_sum_mem_spanBall_one (A := ∅) (B := {w}) (Finset.empty_subset V)
    (Finset.singleton_subset_iff.mpr hw)
  simpa using h

/-- **Adjoining an escaping frequency keeps independence.** -/
theorem subsetSumInjective_insert {G : Type*} [AddCommGroup G] [DecidableEq G] {V : Finset G} {w : G}
    (hV : SubsetSumInjective V) (hw : w ∉ spanBall V 1) :
    SubsetSumInjective (insert w V) := by
  have hwV : w ∉ V := fun h => hw (self_mem_spanBall_one h)
  have herase : ∀ C ⊆ insert w V, C.erase w ⊆ V := by
    intro C hC v hv
    have h1 := Finset.mem_erase.mp hv
    rcases Finset.mem_insert.mp (hC h1.2) with h | h
    · exact absurd h h1.1
    · exact h
  have hsplit : ∀ C : Finset G, w ∈ C → ∑ v ∈ C, v = w + ∑ v ∈ C.erase w, v := by
    intro C hC
    rw [Finset.add_sum_erase C (fun v => v) hC]
  have hsub : ∀ C ⊆ insert w V, w ∉ C → C ⊆ V := by
    intro C hC hwC
    rw [← Finset.erase_eq_of_notMem hwC]
    exact herase C hC
  have hone : ∀ A ⊆ insert w V, ∀ B ⊆ insert w V, w ∈ A → w ∉ B →
      ∑ v ∈ A, v ≠ ∑ v ∈ B, v := by
    intro A hA B hB hwA hwB hsum
    apply hw
    have h := sub_sum_mem_spanBall_one (herase A hA) (hsub B hB hwB)
    have : ∑ v ∈ B, v - ∑ v ∈ A.erase w, v = w := by
      rw [← hsum, hsplit A hwA]; abel
    rwa [this] at h
  intro A hA B hB hsum
  by_cases hwA : w ∈ A <;> by_cases hwB : w ∈ B
  · have h : A.erase w = B.erase w := by
      apply hV _ (herase A hA) _ (herase B hB)
      rw [hsplit A hwA, hsplit B hwB] at hsum
      exact add_left_cancel hsum
    rw [← Finset.insert_erase hwA, ← Finset.insert_erase hwB, h]
  · exact absurd hsum (hone A hA B hB hwA hwB)
  · exact absurd hsum.symm (hone B hB A hA hwB hwA)
  · exact hV A (hsub A hA hwA) B (hsub B hB hwB) hsum

/-- **The independence cap.** -/
theorem card_le_of_subsetSumInjective {G : Type*} [AddCommGroup G] (Γ : Finset G) (R : Nat)
    {V : Finset G} (hVΓ : V ⊆ spanBall Γ R) (hV : SubsetSumInjective V) :
    2 ^ V.card ≤ (2 * V.card * R + 1) ^ Γ.card := by
  let e := V.equivFin
  let v : Fin V.card → G := fun i => (e.symm i : G)
  have hvinj : Function.Injective v := fun i j h => e.symm.injective (Subtype.ext h)
  refine independent_card_le Γ R V.card v (fun i => hVΓ (e.symm i).2) ?_
  intro ε ε' h
  simp only at h
  let A := (Finset.univ.filter fun i => ε i = true).image v
  let B := (Finset.univ.filter fun i => ε' i = true).image v
  have hsumA : ∑ i, (if ε i then v i else 0) = ∑ x ∈ A, x := by
    rw [Finset.sum_image (fun i _ j _ h => hvinj h), Finset.sum_filter]
  have hsumB : ∑ i, (if ε' i then v i else 0) = ∑ x ∈ B, x := by
    rw [Finset.sum_image (fun i _ j _ h => hvinj h), Finset.sum_filter]
  have hAV : A ⊆ V := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact (e.symm i).2
  have hBV : B ⊆ V := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact (e.symm i).2
  have hAB : A = B := hV A hAV B hBV (by rw [← hsumA, ← hsumB]; exact h)
  funext i
  have hiff : ε i = true ↔ ε' i = true := by
    constructor
    · intro hi
      have : v i ∈ B := hAB ▸ Finset.mem_image_of_mem v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp this
      rw [← hvinj hji]
      exact (Finset.mem_filter.mp hj).2
    · intro hi
      have : v i ∈ A := hAB.symm ▸ Finset.mem_image_of_mem v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp this
      rw [← hvinj hji]
      exact (Finset.mem_filter.mp hj).2
  cases h1 : ε i <;> cases h2 : ε' i <;> simp_all

end LeanProofs.GowersSzemeredi
