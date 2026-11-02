import DiophantineConsistency.CompactTableLookup
import DiophantineConsistency.MFWangTiles942Core
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
noncomputable section
namespace CompactRowTransport
open DiophantineConsistency CompactRelabelDraft
open DiophantineConsistency.ArithmeticWangTable

theorem row_at (m : ℕ) (hm : m < 942) :
    translated (tileN m) =
      Compact943Data.rows.toArray[rowIndices.toList.getD m 0]?.getD (0,0,0,0) := by
  have hr : m < rowIndices.toList.length := by simpa only [CompactTableLookup.row_length] using hm
  have ho : m < WangTiles942.orderedRows.length := by simpa only [WangTiles942.ordered_count] using hm
  have h := congrArg (fun xs => xs[m]?) full_row_equality
  simp only [mappedOld, selectedNew, List.getElem?_map, getElem?_pos WangTiles942.orderedRows m ho,
    getElem?_pos rowIndices.toList m hr, Option.map_some, Option.some.injEq] at h
  simpa only [tileN, dif_pos hm, WangTiles942.tile, List.getD_eq_getElem?_getD,
    getElem?_pos rowIndices.toList m hr, Option.getD_some] using h
#print axioms CompactRowTransport.row_at
end CompactRowTransport

namespace CompactRowTransport
open DiophantineConsistency CompactRelabelDraft
open DiophantineConsistency.ArithmeticWangTable
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
abbrev Quad := ℕ × ℕ × ℕ × ℕ
noncomputable def compactField (f : Quad → ℕ) (i : V) : V :=
  tabValue (Compact943Data.rows.map f) 0 i

theorem compactField_cast (f : Quad → ℕ) (hf : f (0,0,0,0) = 0) (m : ℕ) :
    compactField f (m : V) = ((f (Compact943Data.rows.toArray[m]?.getD (0,0,0,0))) : V) := by
  dsimp only [compactField]
  rw [tab_cast, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : Compact943Data.rows[m]? <;> simp [h, hf]

theorem bounded_row_fields {i : V} (hi : i < 942) :
    ∃ m : ℕ, m < 942 ∧ i = (m : V) ∧
      (let j := rowIndices.toList.getD m 0
       CompactTableLookup.rowLookup i = (j : V) ∧
       translated (tileN m) = Compact943Data.rows.toArray[j]?.getD (0,0,0,0)) := by
  obtain ⟨m, hm, rfl⟩ := standard_of_lt (n := 942) (by simpa using hi)
  refine ⟨m, hm, rfl, ?_⟩
  constructor
  · exact tab_cast _ _
  · exact row_at m hm
theorem bounded_field_transport (f : Quad → ℕ) (hf : f (0,0,0,0) = 0)
    {i : V} (hi : i < 942) :
    ∃ m : ℕ, m < 942 ∧ i = (m : V) ∧
      compactField f (CompactTableLookup.rowLookup i) = ((f (translated (tileN m))) : V) := by
  obtain ⟨m, hm, hindex, hrow, htile⟩ := bounded_row_fields hi
  refine ⟨m, hm, hindex, ?_⟩
  rw [hrow, compactField_cast f hf, htile]
#print axioms CompactRowTransport.bounded_field_transport
#print axioms CompactRowTransport.compactField_cast
#print axioms CompactRowTransport.bounded_row_fields
end CompactRowTransport
namespace CompactRowTransport
open DiophantineConsistency CompactRelabelDraft
open DiophantineConsistency.ArithmeticWangTable CompactTableLookup
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem four_fields {i : V} (hi : i < 942) :
    compactField (fun t => t.1) (rowLookup i) = horizontalLookup (westC i) ∧
    compactField (fun t => t.2.1) (rowLookup i) = verticalLookup (northC i) ∧
    compactField (fun t => t.2.2.1) (rowLookup i) = horizontalLookup (eastC i) ∧
    compactField (fun t => t.2.2.2) (rowLookup i) = verticalLookup (southC i) := by
  obtain ⟨m, hm, rfl⟩ := standard_of_lt (n := 942) (by simpa using hi)
  have h (f : Quad → ℕ) (hf : f (0,0,0,0) = 0) :
      compactField f (rowLookup (m : V)) = (f (translated (tileN m)) : V) := by
    obtain ⟨n,hn,he,hfieldeq⟩ := bounded_field_transport f hf (i := (m : V)) (by exact_mod_cast hm)
    have hmn : m = n := by exact_mod_cast he
    simpa only [← hmn] using hfieldeq
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h (fun t => t.1) rfl, westC_cast, horizontalLookup, tab_cast]
    simp [translated, List.getD_eq_getElem?_getD]
  · rw [h (fun t => t.2.1) rfl, northC_cast, verticalLookup, tab_cast]
    simp [translated, List.getD_eq_getElem?_getD]
  · rw [h (fun t => t.2.2.1) rfl, eastC_cast, horizontalLookup, tab_cast]
    simp [translated, List.getD_eq_getElem?_getD]
  · rw [h (fun t => t.2.2.2) rfl, southC_cast, verticalLookup, tab_cast]
    simp [translated, List.getD_eq_getElem?_getD]
#print axioms CompactRowTransport.four_fields
end CompactRowTransport
namespace CompactRowTransport
open DiophantineConsistency.ArithmeticWangTable CompactTableLookup
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem horizontal_match_iff {i j : V} (hi : i < 942) (hj : j < 942)
    (he : eastC i < 250) (hw : westC j < 250) :
    compactField (fun t => t.2.2.1) (rowLookup i) =
      compactField (fun t => t.1) (rowLookup j) ↔ eastC i = westC j := by
  rw [(four_fields hi).2.2.1, (four_fields hj).1]
  constructor
  · exact horizontal_injective he hw
  · intro h; rw [h]

theorem vertical_match_iff {i j : V} (hi : i < 942) (hj : j < 942)
    (hs : southC i < 439) (hn : northC j < 439) :
    compactField (fun t => t.2.2.2) (rowLookup i) =
      compactField (fun t => t.2.1) (rowLookup j) ↔ southC i = northC j := by
  rw [(four_fields hi).2.2.2, (four_fields hj).2.1]
  constructor
  · exact vertical_injective hs hn
  · intro h; rw [h]
#print axioms CompactRowTransport.horizontal_match_iff
#print axioms CompactRowTransport.vertical_match_iff
end CompactRowTransport

namespace CompactRowTransport
open DiophantineConsistency
open DiophantineConsistency.ArithmeticWangTable
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem vertical_bounds {i : V} (hi : i < 942) : northC i < 439 ∧ southC i < 439 := by
  obtain ⟨m, hm, rfl⟩ := standard_of_lt (n := 942) (by simpa using hi)
  obtain ⟨row, hmem, hrow⟩ := tileN_mem m hm
  have ht := MF.WangTiles942.all_rows_tight row hmem
  rw [hrow] at ht
  simp only [MF.WangTiles942.TightColorsBounded] at ht
  have hn : (tileN m).north < 439 := by omega
  have hs : (tileN m).south < 439 := by omega
  rw [northC_cast, southC_cast]
  constructor
  · exact_mod_cast hn
  · exact_mod_cast hs
#print axioms CompactRowTransport.vertical_bounds
end CompactRowTransport

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace CompactHorizontalCore
open DiophantineConsistency DiophantineConsistency.WangTiles942
open DiophantineConsistency.MF.WangTiles942

def HorizontalBounded (t : Tile) : Prop := t.west < 250 ∧ t.east < 250
instance (t : Tile) : Decidable (HorizontalBounded t) := inferInstanceAs (Decidable (t.west < 250 ∧ t.east < 250))

theorem action_target_mem (j : Fin 430) : (action j).2.2 ∈ targets (action j).2.1 := by
  rw [targets_eq_cache]
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨action j, ?_, rfl⟩
  apply List.mem_filter.mpr
  exact ⟨List.mem_ofFn.mpr ⟨j, rfl⟩, by simp⟩

theorem rail_lt_250 {d : Bool} {q : ℕ} (hq : q ∈ targets d) : rail d q < 250 := by
  have hc : (targets d ∩ Finset.range q).card < (targets d).card := by
    apply Finset.card_lt_card
    exact (Finset.ssubset_iff_of_subset Finset.inter_subset_left).2 ⟨q, hq, by simp⟩
  rw [rail_eq_formula]
  cases d
  · rw [target_counts.1] at hc
    simp only [railFormula, Bool.toNat_false, Nat.mul_zero, Nat.sub_zero]
    omega
  · rw [target_counts.2] at hc
    simp only [railFormula, Bool.toNat_true, Nat.mul_one]
    omega

theorem transition_bounded (j : Fin 430) : HorizontalBounded (transitionRow j).2 := by
  have h := rail_lt_250 (action_target_mem j)
  dsimp only [transitionRow, HorizontalBounded]
  cases hd : (action j).2.1 <;>
    simp only [hd, Bool.toNat_false, Bool.toNat_true, Nat.sub_zero, Nat.sub_self,
      Nat.one_mul, Nat.zero_mul] at * <;> omega

theorem copies_bounded : ∀ a : Fin 2, ∀ row ∈ copyRows a.val, HorizontalBounded row.2 := by
  decide +kernel

theorem signals_bounded (d : Bool) : ∀ row ∈ signalRows d, HorizontalBounded row.2 := by
  intro row hrow
  obtain ⟨q,hq,hr⟩ := List.mem_flatMap.mp hrow
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hr
  have hr' := rail_lt_250 (List.mem_toFinset.mpr hq)
  dsimp only [HorizontalBounded]
  cases d <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.sub_zero, Nat.sub_self,
      Nat.one_mul, Nat.zero_mul] at * <;> omega

theorem tail_bounded : ∀ row ∈ tailRows, HorizontalBounded row.2 := by decide +kernel

theorem all_rows_bounded : ∀ row ∈ orderedRows, HorizontalBounded row.2 := by
  simp only [orderedRows, List.forall_mem_append]
  exact ⟨⟨⟨⟨by decide +kernel, List.forall_mem_ofFn_iff.mpr transition_bounded⟩,
    ⟨copies_bounded 1, copies_bounded 0⟩⟩,
    ⟨signals_bounded true, signals_bounded false⟩⟩, tail_bounded⟩
#print axioms CompactHorizontalCore.all_rows_bounded
end CompactHorizontalCore
namespace CompactRowTransport
open DiophantineConsistency
open DiophantineConsistency.ArithmeticWangTable
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem horizontal_bounds {i : V} (hi : i < 942) : westC i < 250 ∧ eastC i < 250 := by
  obtain ⟨m, hm, rfl⟩ := standard_of_lt (n := 942) (by simpa using hi)
  obtain ⟨row, hmem, hrow⟩ := tileN_mem m hm
  have ht := CompactHorizontalCore.all_rows_bounded row hmem
  rw [hrow] at ht
  simp only [CompactHorizontalCore.HorizontalBounded] at ht
  rw [westC_cast, eastC_cast]
  constructor
  · exact_mod_cast ht.1
  · exact_mod_cast ht.2

theorem horizontal_match_bounded {i j : V} (hi : i < 942) (hj : j < 942) :
    compactField (fun t => t.2.2.1) (CompactTableLookup.rowLookup i) =
      compactField (fun t => t.1) (CompactTableLookup.rowLookup j) ↔ eastC i = westC j :=
  horizontal_match_iff hi hj (horizontal_bounds hi).2 (horizontal_bounds hj).1

theorem vertical_match_bounded {i j : V} (hi : i < 942) (hj : j < 942) :
    compactField (fun t => t.2.2.2) (CompactTableLookup.rowLookup i) =
      compactField (fun t => t.2.1) (CompactTableLookup.rowLookup j) ↔ southC i = northC j :=
  vertical_match_iff hi hj (vertical_bounds hi).2 (vertical_bounds hj).1
#print axioms CompactRowTransport.horizontal_bounds
#print axioms CompactRowTransport.horizontal_match_bounded
#print axioms CompactRowTransport.vertical_match_bounded
end CompactRowTransport
