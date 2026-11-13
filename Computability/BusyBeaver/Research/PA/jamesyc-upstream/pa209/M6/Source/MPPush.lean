module
public import M6.Source.AXPushParam
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace M6.Source.MPPush

private theorem row0 : resolveAt exactSites 3818 =
    some (AXPushParam.relocate 3793 (AXPush.expected 0)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row1 : resolveAt exactSites 3819 =
    some (AXPushParam.relocate 3793 (AXPush.expected 1)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row2 : resolveAt exactSites 3820 =
    some (AXPushParam.relocate 3793 (AXPush.expected 2)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3 : resolveAt exactSites 3821 =
    some (AXPushParam.relocate 3793 (AXPush.expected 3)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row4 : resolveAt exactSites 3822 =
    some (AXPushParam.relocate 3793 (AXPush.expected 4)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row5 : resolveAt exactSites 3823 =
    some (AXPushParam.relocate 3793 (AXPush.expected 5)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row6 : resolveAt exactSites 3824 =
    some (AXPushParam.relocate 3793 (AXPush.expected 6)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row7 : resolveAt exactSites 3825 =
    some (AXPushParam.relocate 3793 (AXPush.expected 7)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row8 : resolveAt exactSites 3826 =
    some (AXPushParam.relocate 3793 (AXPush.expected 8)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row9 : resolveAt exactSites 3827 =
    some (AXPushParam.relocate 3793 (AXPush.expected 9)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row10 : resolveAt exactSites 3828 =
    some (AXPushParam.relocate 3793 (AXPush.expected 10)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row11 : resolveAt exactSites 3829 =
    some (AXPushParam.relocate 3793 (AXPush.expected 11)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row12 : resolveAt exactSites 3830 =
    some (AXPushParam.relocate 3793 (AXPush.expected 12)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row13 : resolveAt exactSites 3831 =
    some (AXPushParam.relocate 3793 (AXPush.expected 13)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row14 : resolveAt exactSites 3832 =
    some (AXPushParam.relocate 3793 (AXPush.expected 14)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row15 : resolveAt exactSites 3833 =
    some (AXPushParam.relocate 3793 (AXPush.expected 15)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row16 : resolveAt exactSites 3834 =
    some (AXPushParam.relocate 3793 (AXPush.expected 16)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row17 : resolveAt exactSites 3835 =
    some (AXPushParam.relocate 3793 (AXPush.expected 17)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row18 : resolveAt exactSites 3836 =
    some (AXPushParam.relocate 3793 (AXPush.expected 18)) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl

theorem bound : AXPushParam.Bound exactSites 3793 := by
  intro ⟨j,hj⟩
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14
  · exact row15
  · exact row16
  · exact row17
  · exact row18

/-- Actual MP push at3818–3836. The entire unrelated register frame is preserved. -/
theorem push (t w : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps exactSites n
      ⟨.at 3818,AXPush.registers ⟨t,w,0,0,f⟩⟩
      ⟨.at 3837,AXPush.registers ⟨0,Cantor.pair t w,0,0,f⟩⟩ := by
  exact AXPushParam.push bound t w f

#print axioms bound
#print axioms push
end M6.Source.MPPush

