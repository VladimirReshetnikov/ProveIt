import GowersSzemeredi.Proofs16ColumnWordDensity

/-! A bounded disjoint subfamily meets every member of a dense finite family. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

/-- Maximal disjoint packing gives at most `1/delta` models, with a
nonempty intersection witnessing the model chosen for every family. -/
theorem dense_family_packing {I U : Type*} (A : Finset I) (Omega : Finset U)
    (F : I → Finset U) {delta M : Real} (hd : 0 < delta) (hM : 0 < M)
    (hOmega : (Omega.card : Real) ≤ M)
    (hsub : ∀ i ∈ A, F i ⊆ Omega) (hmass : ∀ i ∈ A, delta*M ≤ (F i).card) :
    ∃ J ⊆ A, (↑J : Set I).PairwiseDisjoint F ∧ (J.card : Real)*delta ≤ 1 ∧
      ∀ i ∈ A, ∃ j ∈ J, (F i ∩ F j).Nonempty := by
  let C := A.powerset.filter (fun (J : Finset I) => (↑J : Set I).PairwiseDisjoint F)
  have hC : C.Nonempty := ⟨∅,by simp [C]⟩
  obtain ⟨J,hJ,hmax⟩ := Finset.exists_max_image C Finset.card hC
  obtain ⟨hJA,hdis⟩ := Finset.mem_filter.mp hJ
  have hJA' : J ⊆ A := Finset.mem_powerset.mp hJA
  have hcover : ∀ i ∈ A, ∃ j ∈ J, (F i ∩ F j).Nonempty := by
    intro i hi
    by_contra hn
    have hno : ∀ j ∈ J, Disjoint (F i) (F j) := by
      intro j hj
      apply Finset.disjoint_left.mpr
      intro x hxi hxj
      exact hn ⟨j,hj,⟨x,Finset.mem_inter.mpr ⟨hxi,hxj⟩⟩⟩
    have hne : (F i).Nonempty := by
      apply Finset.card_pos.mp
      have h : (0 : Real) < (F i).card := (mul_pos hd hM).trans_le (hmass i hi)
      exact_mod_cast h
    have hin : i ∉ J := by
      intro hij
      obtain ⟨x,hx⟩ := hne
      exact Finset.disjoint_left.mp (hno i hij) hx hx
    have hins : insert i J ∈ C := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset hi hJA'),?_⟩
      intro j hj l hl hjl
      by_cases hji : j = i
      · subst j
        exact hno l ((Finset.mem_insert.mp hl).resolve_left (Ne.symm hjl))
      by_cases hli : l = i
      · subst l
        exact (hno j ((Finset.mem_insert.mp hj).resolve_left hji)).symm
      exact hdis ((Finset.mem_insert.mp hj).resolve_left hji)
        ((Finset.mem_insert.mp hl).resolve_left hli) hjl
    have h := hmax (insert i J) hins
    rw [Finset.card_insert_of_notMem hin] at h
    omega
  have hunion : J.biUnion F ⊆ Omega := by
    intro x hx
    obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
    exact hsub i (hJA' hi) hx
  have hsum : (∑ i ∈ J, ((F i).card : Real)) ≤ M := by
    have hc : (∑ i ∈ J, (F i).card) ≤ Omega.card := by
      rw [← Finset.card_biUnion hdis]
      exact Finset.card_le_card hunion
    exact (by exact_mod_cast hc : (∑ i ∈ J, ((F i).card : Real)) ≤ Omega.card).trans hOmega
  have hsmall : (J.card : Real)*delta ≤ 1 := by
    have hm : (J.card : Real)*(delta*M) ≤ ∑ i ∈ J, ((F i).card : Real) := by
      calc _ = ∑ _i ∈ J, delta*M := by simp
        _ ≤ _ := Finset.sum_le_sum fun i hi => hmass i (hJA' hi)
    apply (mul_le_mul_iff_left₀ hM).mp
    nlinarith
  exact ⟨J,hJA',hdis,hsmall,hcover⟩

end LeanProofs.GowersSzemeredi
