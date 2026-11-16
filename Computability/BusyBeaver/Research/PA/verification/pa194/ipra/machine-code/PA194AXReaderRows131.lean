import PA194SourceProgram
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194AXReaderRows
open M6.Source
theorem s131 :
    (PathTrie.nthSite PA194.SourceTree.trie 131).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 8 (some 139) (some 132)) := by decide +kernel
theorem s132 :
    (PathTrie.nthSite PA194.SourceTree.trie 132).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 7 (some 133)) := by decide +kernel
theorem s133 :
    (PathTrie.nthSite PA194.SourceTree.trie 133).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 6 (some 135) (some 134)) := by decide +kernel
theorem s134 :
    (PathTrie.nthSite PA194.SourceTree.trie 134).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 138)) := by decide +kernel
theorem s135 :
    (PathTrie.nthSite PA194.SourceTree.trie 135).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 7 (some 138) (some 136)) := by decide +kernel
theorem s136 :
    (PathTrie.nthSite PA194.SourceTree.trie 136).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 6 (some 137)) := by decide +kernel
theorem s137 :
    (PathTrie.nthSite PA194.SourceTree.trie 137).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 135)) := by decide +kernel
theorem s138 :
    (PathTrie.nthSite PA194.SourceTree.trie 138).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 131)) := by decide +kernel
theorem s139 :
    (PathTrie.nthSite PA194.SourceTree.trie 139).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 7 (some 142) (some 140)) := by decide +kernel
theorem s140 :
    (PathTrie.nthSite PA194.SourceTree.trie 140).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 8 (some 141)) := by decide +kernel
theorem s141 :
    (PathTrie.nthSite PA194.SourceTree.trie 141).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 139)) := by decide +kernel
theorem s142 :
    (PathTrie.nthSite PA194.SourceTree.trie 142).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 6 (some 145) (some 143)) := by decide +kernel
theorem s143 :
    (PathTrie.nthSite PA194.SourceTree.trie 143).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 5 (some 144)) := by decide +kernel
theorem s144 :
    (PathTrie.nthSite PA194.SourceTree.trie 144).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 142)) := by decide +kernel
#print axioms s131
#print axioms s144
end PA194AXReaderRows
