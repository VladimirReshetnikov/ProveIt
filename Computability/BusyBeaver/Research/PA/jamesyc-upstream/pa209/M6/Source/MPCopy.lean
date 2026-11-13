module
public import M6.Source.CopyToT
public import M6.Source.ExactSource
public import M6.Source.TrieResolver
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace M6.Source.MPCopy
private theorem first_row0 : resolveAt exactSites 3837 = some (CopyToT.expected 4 3837 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem first_row1 : resolveAt exactSites 3838 = some (CopyToT.expected 4 3837 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem first_row2 : resolveAt exactSites 3839 = some (CopyToT.expected 4 3837 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem first_row3 : resolveAt exactSites 3840 = some (CopyToT.expected 4 3837 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem first_row4 : resolveAt exactSites 3841 = some (CopyToT.expected 4 3837 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem first_row5 : resolveAt exactSites 3842 = some (CopyToT.expected 4 3837 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem first_row6 : resolveAt exactSites 3843 = some (CopyToT.expected 4 3837 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem first_bound : CopyToT.Bound exactSites 4 3837 := by
  intro ⟨j,hj⟩
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact first_row0
  · exact first_row1
  · exact first_row2
  · exact first_row3
  · exact first_row4
  · exact first_row5
  · exact first_row6
theorem first_copy (d t : Nat) (f : Registers) :
    Steps exactSites (7*d+2) (CopyToT.config 4 3837 0 d t 0 f)
      (CopyToT.config 4 3837 7 d (t+d) 0 f) :=
  CopyToT.copy (by decide) (by decide) first_bound d t f
#print axioms first_copy
private theorem last_row0 : resolveAt exactSites 3903 = some (CopyToT.expected 4 3903 0) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem last_row1 : resolveAt exactSites 3904 = some (CopyToT.expected 4 3903 1) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem last_row2 : resolveAt exactSites 3905 = some (CopyToT.expected 4 3903 2) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem last_row3 : resolveAt exactSites 3906 = some (CopyToT.expected 4 3903 3) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem last_row4 : resolveAt exactSites 3907 = some (CopyToT.expected 4 3903 4) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem last_row5 : resolveAt exactSites 3908 = some (CopyToT.expected 4 3903 5) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
private theorem last_row6 : resolveAt exactSites 3909 = some (CopyToT.expected 4 3903 6) := by
  rw [← PathTrie.fastResolveAt_eq]
  rfl
theorem last_bound : CopyToT.Bound exactSites 4 3903 := by
  intro ⟨j,hj⟩
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact last_row0
  · exact last_row1
  · exact last_row2
  · exact last_row3
  · exact last_row4
  · exact last_row5
  · exact last_row6
theorem last_copy (d t : Nat) (f : Registers) :
    Steps exactSites (7*d+2) (CopyToT.config 4 3903 0 d t 0 f)
      (CopyToT.config 4 3903 7 d (t+d) 0 f) :=
  CopyToT.copy (by decide) (by decide) last_bound d t f
#print axioms last_copy
end M6.Source.MPCopy

