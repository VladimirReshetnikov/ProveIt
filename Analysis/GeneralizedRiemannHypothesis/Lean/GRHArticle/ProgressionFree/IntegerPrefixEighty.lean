import GRHArticle.ProgressionFree.IntegerPrefix

/-!
# The 80-term integer prefix certificates

The cardinality certificates provide admissible prefixes at every cutoff.
The weighted certificate uses disjoint forbidden triples to lower-bound
the cost on branches of the cover search.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

private def minimumVertexCost (w : ℕ → ℕ) (e : IntegerPrefixTriple) : ℕ :=
  min (w e.first) (min (w e.middle) (w e.last))

private theorem minimumVertexCost_le (w : ℕ → ℕ) (e : IntegerPrefixTriple)
    {x : ℕ} (hx : x ∈ e.vertices) : minimumVertexCost w e ≤ w x := by
  simp only [IntegerPrefixTriple.vertices, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

private def greedyPackingCost (w : ℕ → ℕ) :
    List ℕ → List IntegerPrefixTriple → ℕ
  | _, [] => 0
  | seen, e::es =>
    if e.vertices.any seen.contains then greedyPackingCost w seen es
    else minimumVertexCost w e + greedyPackingCost w (e.vertices ++ seen) es

private theorem greedyPackingCost_le (w : ℕ → ℕ) (C : Finset ℕ) (seen : List ℕ)
    (es : List IntegerPrefixTriple)
    (hC : ∀ e ∈ es, (∀ x ∈ e.vertices, x ∉ seen) → ∃ x ∈ e.vertices, x ∈ C) :
    greedyPackingCost w seen es ≤ ∑ x ∈ C, w x := by
  induction es generalizing C seen with
  | nil => exact Nat.zero_le _
  | cons e es ih =>
    unfold greedyPackingCost
    split
    · exact ih C seen (fun e he ↦ hC e (List.mem_cons_of_mem _ he))
    · next hd =>
      have hdis : ∀ x ∈ e.vertices, x ∉ seen := by
        intro x hx hseen
        exact hd (List.any_eq_true.mpr ⟨x, hx, List.contains_iff_mem.mpr hseen⟩)
      obtain ⟨x, hx, hxC⟩ := hC e (List.mem_cons_self) hdis
      have hrec := ih (C.erase x) (e.vertices ++ seen) (by
        intro t ht hd
        obtain ⟨y, hy, hyC⟩ := hC t (List.mem_cons_of_mem _ ht) (fun y hy hys ↦
          hd y hy (List.mem_append.mpr (Or.inr hys)))
        refine ⟨y, hy, mem_erase.mpr ⟨?_, hyC⟩⟩
        intro heq
        exact hd y hy (List.mem_append.mpr (Or.inl (heq ▸ hx))))
      have hcost := minimumVertexCost_le w e hx
      have hsum := sum_erase_add C w hxC
      omega

private def rejectCoverBudget (w : ℕ → ℕ) :
    ℕ → ℕ → List IntegerPrefixTriple → Bool
  | 0, _, _ => false
  | _+1, _, [] => false
  | f+1, b, e::es =>
    if b < greedyPackingCost w [] (e::es) then true
    else e.vertices.all fun x ↦ decide (b < w x) ||
      rejectCoverBudget w f (b-w x) (es.filter fun t ↦ !t.vertices.contains x)

private theorem rejectCoverBudget_sound {w : ℕ → ℕ} {C : Finset ℕ} {b f : ℕ}
    {es : List IntegerPrefixTriple}
    (h : rejectCoverBudget w f b es = true) (hC : integerPrefixCovers C es) :
    b < ∑ x ∈ C, w x := by
  induction f generalizing b C es with
  | zero => simp [rejectCoverBudget] at h
  | succ f ih =>
    cases es with
    | nil => simp [rejectCoverBudget] at h
    | cons e es =>
      unfold rejectCoverBudget at h
      split at h
      · next hp =>
        exact hp.trans_le (greedyPackingCost_le w C [] (e::es) (fun t ht _ ↦ hC t ht))
      · obtain ⟨x, hx, hxC⟩ := hC e List.mem_cons_self
        have hw := sum_erase_add C w hxC
        have hcase := List.all_eq_true.mp h x hx
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hcase
        rcases hcase with hx | hrec
        · omega
        · have hr := ih (C := C.erase x) hrec (by
            intro t ht
            obtain ⟨ht, hnt⟩ := List.mem_filter.mp ht
            obtain ⟨y, hy, hyC⟩ := hC t (List.mem_cons_of_mem _ ht)
            have hnx : x ∉ t.vertices := by simpa using hnt
            exact ⟨y, hy, mem_erase.mpr ⟨fun he ↦ hnx (he ▸ hy), hyC⟩⟩)
          omega

private def eightyRationalEdges : List IntegerPrefixTriple :=
  [⟨1,2,4⟩, ⟨1,3,9⟩, ⟨1,4,16⟩, ⟨1,5,25⟩, ⟨1,6,36⟩, ⟨1,7,49⟩,
    ⟨1,8,64⟩, ⟨2,4,8⟩, ⟨2,6,18⟩, ⟨2,8,32⟩, ⟨2,10,50⟩, ⟨2,12,72⟩,
    ⟨3,6,12⟩, ⟨3,9,27⟩, ⟨3,12,48⟩, ⟨3,15,75⟩, ⟨4,6,9⟩, ⟨4,8,16⟩,
    ⟨4,10,25⟩, ⟨4,12,36⟩, ⟨4,14,49⟩, ⟨4,16,64⟩, ⟨5,10,20⟩, ⟨5,15,45⟩,
    ⟨5,20,80⟩, ⟨6,12,24⟩, ⟨6,18,54⟩, ⟨7,14,28⟩, ⟨7,21,63⟩, ⟨8,12,18⟩,
    ⟨8,16,32⟩, ⟨8,20,50⟩, ⟨8,24,72⟩, ⟨9,12,16⟩, ⟨9,15,25⟩, ⟨9,18,36⟩,
    ⟨9,21,49⟩, ⟨9,24,64⟩, ⟨10,20,40⟩, ⟨11,22,44⟩, ⟨12,18,27⟩, ⟨12,24,48⟩,
    ⟨12,30,75⟩, ⟨13,26,52⟩, ⟨14,28,56⟩, ⟨15,30,60⟩, ⟨16,20,25⟩, ⟨16,24,36⟩,
    ⟨16,28,49⟩, ⟨16,32,64⟩, ⟨17,34,68⟩, ⟨18,24,32⟩, ⟨18,30,50⟩, ⟨18,36,72⟩,
    ⟨19,38,76⟩, ⟨20,30,45⟩, ⟨20,40,80⟩, ⟨24,36,54⟩, ⟨25,30,36⟩, ⟨25,35,49⟩,
    ⟨25,40,64⟩, ⟨27,36,48⟩, ⟨27,45,75⟩, ⟨28,42,63⟩, ⟨32,40,50⟩, ⟨32,48,72⟩,
    ⟨36,42,49⟩, ⟨36,48,64⟩, ⟨45,60,80⟩, ⟨48,60,75⟩, ⟨49,56,64⟩, ⟨50,60,72⟩]

private def eightyIntegralEdges : List IntegerPrefixTriple :=
  [⟨1,2,4⟩, ⟨1,3,9⟩, ⟨1,4,16⟩, ⟨1,5,25⟩, ⟨1,6,36⟩, ⟨1,7,49⟩,
    ⟨1,8,64⟩, ⟨2,4,8⟩, ⟨2,6,18⟩, ⟨2,8,32⟩, ⟨2,10,50⟩, ⟨2,12,72⟩,
    ⟨3,6,12⟩, ⟨3,9,27⟩, ⟨3,12,48⟩, ⟨3,15,75⟩, ⟨4,8,16⟩, ⟨4,12,36⟩,
    ⟨4,16,64⟩, ⟨5,10,20⟩, ⟨5,15,45⟩, ⟨5,20,80⟩, ⟨6,12,24⟩, ⟨6,18,54⟩,
    ⟨7,14,28⟩, ⟨7,21,63⟩, ⟨8,16,32⟩, ⟨8,24,72⟩, ⟨9,18,36⟩, ⟨10,20,40⟩,
    ⟨11,22,44⟩, ⟨12,24,48⟩, ⟨13,26,52⟩, ⟨14,28,56⟩, ⟨15,30,60⟩, ⟨16,32,64⟩,
    ⟨17,34,68⟩, ⟨18,36,72⟩, ⟨19,38,76⟩, ⟨20,40,80⟩]

private def eightyEdgeList (integral : Bool) : List IntegerPrefixTriple :=
  if integral then eightyIntegralEdges else eightyRationalEdges

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem eightyEdgeList_eq (integral : Bool) :
    eightyEdgeList integral = integerPrefixEdges integral 80 := by
  cases integral <;> decide

private def checkedCover (integral : Bool) (N : ℕ) (C : List ℕ) : Bool :=
  decide (N ≤ 80) &&
    ((eightyEdgeList integral).filter fun e ↦ decide (e.last ≤ N)).all fun e ↦
      e.vertices.any C.contains

private theorem checkedCover_sound {integral : Bool} {N : ℕ} {C : List ℕ}
    (h : checkedCover integral N C = true) :
    integerPrefixCovers C.toFinset (integerPrefixEdges integral N) := by
  simp only [checkedCover, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hN, hcheck⟩ := h
  intro e he
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := mem_integerPrefixEdges.mp he
  have hmem : e ∈ (eightyEdgeList integral).filter (fun e ↦ decide (e.last ≤ N)) := by
    rw [eightyEdgeList_eq, List.mem_filter]
    exact ⟨mem_integerPrefixEdges.mpr ⟨h₁,h₂,h₃,h₄.trans hN,h₅,h₆⟩, decide_eq_true h₄⟩
  obtain ⟨x, hx, hC⟩ := List.any_eq_true.mp (List.all_eq_true.mp hcheck e hmem)
  exact ⟨x, hx, List.mem_toFinset.mpr (List.contains_iff_mem.mp hC)⟩

private theorem integerPrefixEdges_mono (integral : Bool) {n N : ℕ} (hn : n ≤ N) :
    ∀ e ∈ integerPrefixEdges integral n, e ∈ integerPrefixEdges integral N := by
  intro e he
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := mem_integerPrefixEdges.mp he
  exact mem_integerPrefixEdges.mpr ⟨h₁, h₂, h₃, h₄.trans hn, h₅, h₆⟩

private theorem prefixCardMax_ge_of_cover {integral : Bool} {n : ℕ} {C : Finset ℕ}
    (hC : integerPrefixCovers C (integerPrefixEdges integral n)) :
    n - C.card ≤ integerPrefixCardMax integral n := by
  have hyes : integerPrefixCoverFeasible integral n (fun _ ↦ 1) C.card = true := by
    apply integerPrefixCoverFeasible_iff.mpr
    refine ⟨C ∩ integerPrefix n, inter_subset_right, ?_, ?_⟩
    · intro e he
      obtain ⟨x, hx, hxC⟩ := hC e he
      exact ⟨x, hx, mem_inter.mpr ⟨hxC, integerPrefixEdge_vertices_mem he x hx⟩⟩
    · simpa using card_le_card (inter_subset_left : C ∩ integerPrefix n ⊆ C)
  obtain ⟨D, hDV, hD, hDw⟩ := integerPrefixCoverFeasible_iff.mp hyes
  let A := integerPrefix n \ D
  have hAV : A ⊆ integerPrefix n := sdiff_subset
  have hAd : IntegerPrefixAdmissible integral (A : Set ℕ) := by
    intro a b c ha hb hc hab hbc he hd
    have hem : (⟨a,b,c⟩ : IntegerPrefixTriple) ∈ integerPrefixEdges integral n :=
      mem_integerPrefixEdges.mpr ⟨(mem_Icc.mp (hAV ha)).1, hab, hbc,
        (mem_Icc.mp (hAV hc)).2, he, hd⟩
    obtain ⟨x, hx, hxd⟩ := hD _ hem
    simp only [IntegerPrefixTriple.vertices, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact (mem_sdiff.mp (by assumption)).2 hxd
  have hcard : A.card = n - D.card := by
    dsimp [A]
    rw [Finset.card_sdiff_of_subset hDV, integerPrefix, Nat.card_Icc]
    omega
  have hdC : D.card ≤ C.card := by simpa using hDw
  calc
    _ ≤ n - D.card := Nat.sub_le_sub_left hdC n
    _ = A.card := hcard.symm
    _ ≤ _ := integerPrefixCount_le_max hAV hAd

private def rationalCoverStages : List (ℕ × List ℕ) :=
  [(3, []),
    (8, [4]),
    (15, [3, 4]),
    (17, [4, 9, 12]),
    (19, [4, 9, 12, 18]),
    (24, [4, 9, 12, 18, 20]),
    (27, [4, 9, 12, 18, 20, 25]),
    (31, [4, 9, 12, 18, 20, 25, 28]),
    (35, [4, 9, 12, 18, 20, 25, 28, 32]),
    (43, [4, 9, 12, 18, 20, 25, 28, 32, 36]),
    (48, [4, 5, 9, 12, 18, 20, 28, 32, 36, 44]),
    (49, [4, 5, 9, 12, 18, 20, 28, 32, 36, 44, 49]),
    (51, [4, 5, 9, 12, 18, 20, 28, 32, 36, 44, 49, 50]),
    (59, [4, 5, 9, 12, 18, 20, 28, 32, 36, 44, 49, 50, 52]),
    (63, [4, 7, 9, 12, 15, 18, 20, 25, 28, 32, 36, 44, 50, 52]),
    (67, [4, 7, 9, 12, 15, 18, 20, 25, 28, 32, 36, 44, 50, 52, 64]),
    (71, [4, 7, 9, 12, 15, 18, 20, 25, 28, 32, 36, 44, 50, 52, 64, 68]),
    (74, [4, 8, 9, 12, 15, 18, 20, 25, 28, 32, 36, 44, 49, 50, 52, 63, 68]),
    (75, [4, 8, 9, 12, 15, 18, 20, 25, 28, 32, 36, 44, 49, 50, 52, 63, 68, 75]),
    (80, [4, 7, 8, 9, 12, 15, 18, 20, 25, 28, 36, 44, 45, 48, 50, 52, 64, 68, 76])]

private def integralCoverStages : List (ℕ × List ℕ) :=
  [(3, []),
    (8, [4]),
    (17, [3, 4]),
    (19, [4, 6, 9]),
    (27, [4, 5, 6, 9]),
    (31, [4, 5, 6, 9, 28]),
    (39, [4, 5, 6, 9, 28, 32]),
    (43, [4, 6, 9, 20, 25, 28, 32]),
    (47, [4, 5, 6, 9, 20, 28, 32, 44]),
    (51, [4, 5, 6, 7, 9, 10, 12, 32, 44]),
    (62, [1, 8, 10, 12, 15, 18, 27, 28, 44, 52]),
    (63, [1, 8, 10, 12, 15, 18, 27, 28, 44, 52, 63]),
    (67, [1, 4, 9, 10, 12, 15, 18, 28, 32, 44, 52, 63]),
    (75, [1, 8, 10, 12, 15, 18, 27, 28, 44, 52, 63, 64, 68]),
    (79, [1, 8, 10, 12, 15, 18, 27, 28, 44, 52, 63, 64, 68, 76]),
    (80, [1, 2, 3, 4, 15, 18, 20, 24, 28, 32, 44, 52, 63, 68, 76])]

private def coverStages (integral : Bool) : List (ℕ × List ℕ) :=
  if integral then integralCoverStages else rationalCoverStages

private def coverStage (integral : Bool) (k : ℕ) : ℕ × List ℕ :=
  ((coverStages integral).find? fun stage ↦ decide (k ≤ stage.1)).getD (0, [])

private def witnessedCount (integral : Bool) (k : ℕ) : ℕ :=
  k - (coverStage integral k).2.length

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checkedCoverStages (integral : Bool) :
    (coverStages integral).all (fun stage ↦ checkedCover integral stage.1 stage.2) = true := by
  cases integral <;> decide

set_option maxRecDepth 30000 in
private theorem coverStage_mem (integral : Bool) :
    ∀ k : Fin 81, (k : ℕ) ≤ (coverStage integral k).1 ∧
      coverStage integral k ∈ coverStages integral := by
  cases integral <;> decide

private theorem witnessedCount_le (integral : Bool) {k : ℕ} (hk : k ≤ 80) :
    witnessedCount integral k ≤ integerPrefixCardMax integral k := by
  obtain ⟨hbound, hstage⟩ := coverStage_mem integral ⟨k, by omega⟩
  have hC := checkedCover_sound
    (List.all_eq_true.mp (checkedCoverStages integral) (coverStage integral k) hstage)
  have hsub := integerPrefixEdges_mono integral hbound
  change k - (coverStage integral k).2.length ≤ _
  have hCL := List.toFinset_card_le ((coverStage integral k).2)
  exact (Nat.sub_le_sub_left hCL k).trans
    (prefixCardMax_ge_of_cover (fun e he ↦ hC e (hsub e he)))

private def weightedCover : List ℕ :=
  [4,9,12,18,20,25,28,32,36,44,45,49,50,52,60,63,64,68,72,75,76]

private def weightedBudget : ℕ :=
  61921704413 * (integerPrefixWeightScale 80 / 97772875200)

private def orderedIntegralEdges : List IntegerPrefixTriple :=
  (List.range 81).flatMap fun k ↦ (eightyEdgeList true).filter fun e ↦ e.last == k

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem weightedBudget_rejected :
    rejectCoverBudget (integerPrefixScaledWeight 80) orderedIntegralEdges.length
      (weightedBudget-1) orderedIntegralEdges = true := by
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem checkedWeightedCover (integral : Bool) :
    checkedCover integral 80 weightedCover = true := by
  cases integral <;> decide

private theorem weightedCoverCost :
    ∑ a ∈ weightedCover.toFinset, integerPrefixScaledWeight 80 a = weightedBudget := by
  rw [List.sum_toFinset _ (show weightedCover.Nodup by decide)]
  decide

private theorem weightedBudget_feasible (integral : Bool) :
    integerPrefixCoverFeasible integral 80 (integerPrefixScaledWeight 80) weightedBudget = true := by
  apply integerPrefixCoverFeasible_iff.mpr
  refine ⟨weightedCover.toFinset, ?_, checkedCover_sound (checkedWeightedCover integral),
    weightedCoverCost.le⟩
  intro x hx
  have h : ∀ x ∈ weightedCover, x ∈ integerPrefix 80 := by decide
  exact h x (List.mem_toFinset.mp hx)

private theorem weightedBudget_infeasible (integral : Bool) :
    integerPrefixCoverFeasible integral 80 (integerPrefixScaledWeight 80) (weightedBudget-1) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨C, _, hC, hcost⟩ := integerPrefixCoverFeasible_iff.mp h
  have hc : integerPrefixCovers C orderedIntegralEdges := by
    intro e he
    apply hC e
    obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp he
    have hm : e ∈ integerPrefixEdges true 80 := by
      rw [← eightyEdgeList_eq]
      exact (List.mem_filter.mp hk).1
    obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := mem_integerPrefixEdges.mp hm
    exact mem_integerPrefixEdges.mpr ⟨h₁,h₂,h₃,h₄,h₅,fun _ ↦ h₆ rfl⟩
  exact (rejectCoverBudget_sound weightedBudget_rejected hc).not_ge hcost

private theorem sum_integerPrefix_eq_list {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ k ∈ integerPrefix N, f k = ((List.range N).map (fun k ↦ f (1+k))).sum := by
  rw [sum_integerPrefix, ← List.toFinset_range, List.sum_toFinset _ List.nodup_range]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
/-- The exact fixed-set weighted optimum up to 80 is the same for both
ratio conventions. -/
theorem integerPrefixReciprocalMax_eighty (integral : Bool) :
    integerPrefixReciprocalMax integral 80 =
      (464893461515148172578064463064095:ℚ) / 139002253949117069621240452738416 := by
  rw [integerPrefixReciprocalMax,
    integerPrefixWeightMax_of_budget (weightedBudget_feasible integral)
      (Or.inr (weightedBudget_infeasible integral)), sum_integerPrefix_eq_list]
  decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
/-- The article's finite losses at 80, certified from explicit
cardinality witnesses and the exact weighted optimum. -/
theorem integerPrefixLoss_eighty_lower (integral : Bool) :
    (if integral then (16567:ℚ)/132300 else (1553:ℚ)/45360) ≤
      integerPrefixLoss integral 80 := by
  have hsum :
      (∑ k ∈ integerPrefix 80, (witnessedCount integral k : ℚ) / (k*(k+1))) ≤
        ∑ k ∈ integerPrefix 80, (integerPrefixCardMax integral k : ℚ) / (k*(k+1)) := by
    apply sum_le_sum
    intro k hk
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast witnessedCount_le integral (mem_Icc.mp hk).2
  unfold integerPrefixLoss
  rw [integerPrefixReciprocalMax_eighty]
  apply le_trans _ (sub_le_sub_right hsum _)
  rw [sum_integerPrefix_eq_list]
  cases integral <;> decide +kernel

end GRHArticle.ProgressionFree
