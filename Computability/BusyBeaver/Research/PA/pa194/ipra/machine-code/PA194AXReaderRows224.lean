import PA194SourceProgram
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194AXReaderRows
open M6.Source
theorem s224 :
    (PathTrie.nthSite PA194.SourceTree.trie 224).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 8 (some 232) (some 225)) := by decide +kernel
theorem s225 :
    (PathTrie.nthSite PA194.SourceTree.trie 225).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 7 (some 226)) := by decide +kernel
theorem s226 :
    (PathTrie.nthSite PA194.SourceTree.trie 226).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 6 (some 228) (some 227)) := by decide +kernel
theorem s227 :
    (PathTrie.nthSite PA194.SourceTree.trie 227).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 231)) := by decide +kernel
theorem s228 :
    (PathTrie.nthSite PA194.SourceTree.trie 228).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 7 (some 231) (some 229)) := by decide +kernel
theorem s229 :
    (PathTrie.nthSite PA194.SourceTree.trie 229).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 6 (some 230)) := by decide +kernel
theorem s230 :
    (PathTrie.nthSite PA194.SourceTree.trie 230).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 228)) := by decide +kernel
theorem s231 :
    (PathTrie.nthSite PA194.SourceTree.trie 231).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 224)) := by decide +kernel
theorem s232 :
    (PathTrie.nthSite PA194.SourceTree.trie 232).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 7 (some 235) (some 233)) := by decide +kernel
theorem s233 :
    (PathTrie.nthSite PA194.SourceTree.trie 233).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 8 (some 234)) := by decide +kernel
theorem s234 :
    (PathTrie.nthSite PA194.SourceTree.trie 234).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 232)) := by decide +kernel
theorem s235 :
    (PathTrie.nthSite PA194.SourceTree.trie 235).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 6 (some 238) (some 236)) := by decide +kernel
theorem s236 :
    (PathTrie.nthSite PA194.SourceTree.trie 236).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 4 (some 237)) := by decide +kernel
theorem s237 :
    (PathTrie.nthSite PA194.SourceTree.trie 237).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 235)) := by decide +kernel
#print axioms s224
#print axioms s237
end PA194AXReaderRows
