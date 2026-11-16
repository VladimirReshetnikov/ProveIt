module
public import M6.Source.AXGateCompare
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
namespace M6.Source.AXGateCompare
private theorem row3773_0 : resolveAt exactSites 3773 = some (expected 3773 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3773_1 : resolveAt exactSites 3774 = some (expected 3773 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3773_2 : resolveAt exactSites 3775 = some (expected 3773 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3773_3 : resolveAt exactSites 3776 = some (expected 3773 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3773_4 : resolveAt exactSites 3777 = some (expected 3773 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3773_5 : resolveAt exactSites 3778 = some (expected 3773 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3773_6 : resolveAt exactSites 3779 = some (expected 3773 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3773_7 : resolveAt exactSites 3780 = some (expected 3773 7) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3773_8 : resolveAt exactSites 3781 = some (expected 3773 8) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3773_9 : resolveAt exactSites 3782 = some (expected 3773 9) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3773_10 : resolveAt exactSites 3783 = some (expected 3773 10) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3773_11 : resolveAt exactSites 3784 = some (expected 3773 11) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem bound3773 : Bound exactSites 3773 := by
  intro ⟨j,hj⟩
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3773_0
  · exact row3773_1
  · exact row3773_2
  · exact row3773_3
  · exact row3773_4
  · exact row3773_5
  · exact row3773_6
  · exact row3773_7
  · exact row3773_8
  · exact row3773_9
  · exact row3773_10
  · exact row3773_11
theorem compare3773 (t h x : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps exactSites n (configAt 3773 0 ⟨t,h,x,f⟩)
      (configAt 3773 12 ⟨if h=x then 0 else t,0,0,f⟩) :=
  compare bound3773 t h x f
#print axioms compare3773
private theorem row3791_0 : resolveAt exactSites 3791 = some (expected 3791 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3791_1 : resolveAt exactSites 3792 = some (expected 3791 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3791_2 : resolveAt exactSites 3793 = some (expected 3791 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3791_3 : resolveAt exactSites 3794 = some (expected 3791 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3791_4 : resolveAt exactSites 3795 = some (expected 3791 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3791_5 : resolveAt exactSites 3796 = some (expected 3791 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3791_6 : resolveAt exactSites 3797 = some (expected 3791 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3791_7 : resolveAt exactSites 3798 = some (expected 3791 7) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3791_8 : resolveAt exactSites 3799 = some (expected 3791 8) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3791_9 : resolveAt exactSites 3800 = some (expected 3791 9) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3791_10 : resolveAt exactSites 3801 = some (expected 3791 10) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem row3791_11 : resolveAt exactSites 3802 = some (expected 3791 11) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem bound3791 : Bound exactSites 3791 := by
  intro ⟨j,hj⟩
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row3791_0
  · exact row3791_1
  · exact row3791_2
  · exact row3791_3
  · exact row3791_4
  · exact row3791_5
  · exact row3791_6
  · exact row3791_7
  · exact row3791_8
  · exact row3791_9
  · exact row3791_10
  · exact row3791_11
theorem compare3791 (t h x : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps exactSites n (configAt 3791 0 ⟨t,h,x,f⟩)
      (configAt 3791 12 ⟨if h=x then 0 else t,0,0,f⟩) :=
  compare bound3791 t h x f
#print axioms compare3791
end M6.Source.AXGateCompare

