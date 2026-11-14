import PA194SourceProgram
namespace PA194ShiftSource
open M6.Source
def nipExpected : Array Instruction := #[
  .inc 6 (some 3672),
  .dec 5 (some 4) (some 1),
  .dec 6 (some 3) (some 2),
  .jump (some 0),
  .jump (some 5),
  .dec 6 (some 10) (some 5),
  .dec 5 (some 7) (some 6),
  .jump (some 5),
  .dec 6 (some 9) (some 8),
  .jump (some 5),
  .jump (some 11),
  .halt
]

def nipPC (j : Nat) : Nat := if j=0 then 3671 else j-1
theorem nip_resolved_at (j : Fin 12) :
    resolveAt PA194SourceProgram.sites (nipPC j.val) = some nipExpected[j.val] := by
  have h : ∀ j : Fin 12,
      (M6.Source.PathTrie.nthSite PA194.SourceTree.trie (nipPC j.val)).bind
        (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some nipExpected[j.val] := by
    decide +kernel
  rw [PA194SourceProgram.resolve_tree]
  exact h j
end PA194ShiftSource
