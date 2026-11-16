import PA194SourceProgram
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194ShiftReaderRows
open M6.Source
theorem s11 :
    (PathTrie.nthSite PA194.SourceTree.trie 11).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 2 (some 19) (some 12)) := by decide +kernel
theorem s12 :
    (PathTrie.nthSite PA194.SourceTree.trie 12).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 7 (some 13)) := by decide +kernel
theorem s13 :
    (PathTrie.nthSite PA194.SourceTree.trie 13).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 6 (some 15) (some 14)) := by decide +kernel
theorem s14 :
    (PathTrie.nthSite PA194.SourceTree.trie 14).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 18)) := by decide +kernel
theorem s15 :
    (PathTrie.nthSite PA194.SourceTree.trie 15).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 7 (some 18) (some 16)) := by decide +kernel
theorem s16 :
    (PathTrie.nthSite PA194.SourceTree.trie 16).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 6 (some 17)) := by decide +kernel
theorem s17 :
    (PathTrie.nthSite PA194.SourceTree.trie 17).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 15)) := by decide +kernel
theorem s18 :
    (PathTrie.nthSite PA194.SourceTree.trie 18).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 11)) := by decide +kernel
theorem s19 :
    (PathTrie.nthSite PA194.SourceTree.trie 19).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 7 (some 22) (some 20)) := by decide +kernel
theorem s20 :
    (PathTrie.nthSite PA194.SourceTree.trie 20).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 2 (some 21)) := by decide +kernel
theorem s21 :
    (PathTrie.nthSite PA194.SourceTree.trie 21).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 19)) := by decide +kernel
theorem s22 :
    (PathTrie.nthSite PA194.SourceTree.trie 22).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 6 (some 25) (some 23)) := by decide +kernel
theorem s23 :
    (PathTrie.nthSite PA194.SourceTree.trie 23).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 5 (some 24)) := by decide +kernel
theorem s24 :
    (PathTrie.nthSite PA194.SourceTree.trie 24).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 22)) := by decide +kernel
#print axioms s11
#print axioms s24
end PA194ShiftReaderRows
