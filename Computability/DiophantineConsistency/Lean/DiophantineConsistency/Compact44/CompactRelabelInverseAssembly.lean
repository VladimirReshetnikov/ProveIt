import DiophantineConsistency.Compact44.CompactRelabelForward00
import DiophantineConsistency.Compact44.CompactRelabelForward01
import DiophantineConsistency.Compact44.CompactRelabelForward02
import DiophantineConsistency.Compact44.CompactRelabelForward03
import DiophantineConsistency.Compact44.CompactRelabelForward04
import DiophantineConsistency.Compact44.CompactRelabelForward05
import DiophantineConsistency.Compact44.CompactRelabelForward06
import DiophantineConsistency.Compact44.CompactRelabelForward07
import DiophantineConsistency.Compact44.CompactRelabelForward08
import DiophantineConsistency.Compact44.CompactRelabelForward09
import DiophantineConsistency.Compact44.CompactRelabelForward10
import DiophantineConsistency.Compact44.CompactRelabelForward11
import DiophantineConsistency.Compact44.CompactRelabelForward12
import DiophantineConsistency.Compact44.CompactRelabelForward13
import DiophantineConsistency.Compact44.CompactRelabelForward14
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace CompactRelabelDraft

theorem combine_index_take_drop {α : Type*} (a b : List α) (n : ℕ)
    (hhead : a.take n = b.take n) (htail : a.drop n = b.drop n) : a = b := by
  calc
    a = a.take n ++ a.drop n := (List.take_append_drop n a).symm
    _ = b.take n ++ b.drop n := by rw [hhead, htail]
    _ = b := List.take_append_drop n b

theorem forward_lengths : forwardRoundtrip.length = 942 ∧ (List.range 942).length = 942 := by decide +kernel

theorem forward_roundtrip : forwardRoundtrip = List.range 942 := by
  have hleft : (forwardRoundtrip.drop 896).length ≤ 46 := by
    simp only [List.length_drop, forward_lengths.1]; omega
  have hright : ((List.range 942).drop 896).length ≤ 46 := by
    simp only [List.length_drop, forward_lengths.2]; omega
  have h14 : forwardRoundtrip.drop 896 = (List.range 942).drop 896 := by
    simpa only [List.take_of_length_le hleft, List.take_of_length_le hright] using forward_14
  have h13 : forwardRoundtrip.drop 832 = (List.range 942).drop 832 := by
    apply combine_index_take_drop _ _ 64 forward_13
    simpa only [List.drop_drop, show 832 + 64 = 896 by decide] using h14
  have h12 : forwardRoundtrip.drop 768 = (List.range 942).drop 768 := by
    apply combine_index_take_drop _ _ 64 forward_12
    simpa only [List.drop_drop, show 768 + 64 = 832 by decide] using h13
  have h11 : forwardRoundtrip.drop 704 = (List.range 942).drop 704 := by
    apply combine_index_take_drop _ _ 64 forward_11
    simpa only [List.drop_drop, show 704 + 64 = 768 by decide] using h12
  have h10 : forwardRoundtrip.drop 640 = (List.range 942).drop 640 := by
    apply combine_index_take_drop _ _ 64 forward_10
    simpa only [List.drop_drop, show 640 + 64 = 704 by decide] using h11
  have h09 : forwardRoundtrip.drop 576 = (List.range 942).drop 576 := by
    apply combine_index_take_drop _ _ 64 forward_09
    simpa only [List.drop_drop, show 576 + 64 = 640 by decide] using h10
  have h08 : forwardRoundtrip.drop 512 = (List.range 942).drop 512 := by
    apply combine_index_take_drop _ _ 64 forward_08
    simpa only [List.drop_drop, show 512 + 64 = 576 by decide] using h09
  have h07 : forwardRoundtrip.drop 448 = (List.range 942).drop 448 := by
    apply combine_index_take_drop _ _ 64 forward_07
    simpa only [List.drop_drop, show 448 + 64 = 512 by decide] using h08
  have h06 : forwardRoundtrip.drop 384 = (List.range 942).drop 384 := by
    apply combine_index_take_drop _ _ 64 forward_06
    simpa only [List.drop_drop, show 384 + 64 = 448 by decide] using h07
  have h05 : forwardRoundtrip.drop 320 = (List.range 942).drop 320 := by
    apply combine_index_take_drop _ _ 64 forward_05
    simpa only [List.drop_drop, show 320 + 64 = 384 by decide] using h06
  have h04 : forwardRoundtrip.drop 256 = (List.range 942).drop 256 := by
    apply combine_index_take_drop _ _ 64 forward_04
    simpa only [List.drop_drop, show 256 + 64 = 320 by decide] using h05
  have h03 : forwardRoundtrip.drop 192 = (List.range 942).drop 192 := by
    apply combine_index_take_drop _ _ 64 forward_03
    simpa only [List.drop_drop, show 192 + 64 = 256 by decide] using h04
  have h02 : forwardRoundtrip.drop 128 = (List.range 942).drop 128 := by
    apply combine_index_take_drop _ _ 64 forward_02
    simpa only [List.drop_drop, show 128 + 64 = 192 by decide] using h03
  have h01 : forwardRoundtrip.drop 64 = (List.range 942).drop 64 := by
    apply combine_index_take_drop _ _ 64 forward_01
    simpa only [List.drop_drop, show 64 + 64 = 128 by decide] using h02
  have h00 : forwardRoundtrip.drop 0 = (List.range 942).drop 0 := by
    apply combine_index_take_drop _ _ 64 forward_00
    simpa only [List.drop_drop, show 0 + 64 = 64 by decide] using h01
  simpa only [List.drop_zero] using h00

theorem valid_indices : rowIndices.toList.all (fun j => decide (j = 0 ∨ (2 ≤ j ∧ j < 943))) = true := by decide +kernel

theorem index_subset : rowIndices.toList ⊆ compactIndices := by
  intro j hj
  have hv : j = 0 ∨ (2 ≤ j ∧ j < 943) :=
    of_decide_eq_true ((List.all_eq_true.mp valid_indices) j hj)
  simp only [compactIndices, List.mem_append, List.mem_singleton]
  rcases hv with hzero | ⟨hlo, hhi⟩
  · exact Or.inl hzero
  · right
    apply List.mem_range'.2
    refine ⟨j-2, by omega, ?_⟩
    omega

theorem index_nodup : rowIndices.toList.Nodup := by
  apply List.Nodup.of_map (fun j => inverseRows[j]?.getD 999)
  change forwardRoundtrip.Nodup
  rw [forward_roundtrip]
  exact List.nodup_range

theorem index_lengths : compactIndices.length ≤ rowIndices.toList.length := by decide +kernel

theorem indices_permutation : rowIndices.toList.Perm compactIndices :=
  (List.subperm_of_subset index_nodup index_subset).perm_of_length_le index_lengths
end CompactRelabelDraft
#print axioms CompactRelabelDraft.forward_roundtrip
#print axioms CompactRelabelDraft.indices_permutation
