import PA194SourceProgram

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194MPLiteralRows
open M6.Source

theorem s3594 :
    (PathTrie.nthSite PA194.SourceTree.trie 3594).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 2 (some 3602) (some 3595)) := by decide +kernel
theorem s3595 :
    (PathTrie.nthSite PA194.SourceTree.trie 3595).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 7 (some 3596)) := by decide +kernel
theorem s3596 :
    (PathTrie.nthSite PA194.SourceTree.trie 3596).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 6 (some 3598) (some 3597)) := by decide +kernel
theorem s3597 :
    (PathTrie.nthSite PA194.SourceTree.trie 3597).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3601)) := by decide +kernel
theorem s3598 :
    (PathTrie.nthSite PA194.SourceTree.trie 3598).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 7 (some 3601) (some 3599)) := by decide +kernel
theorem s3599 :
    (PathTrie.nthSite PA194.SourceTree.trie 3599).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 6 (some 3600)) := by decide +kernel
theorem s3600 :
    (PathTrie.nthSite PA194.SourceTree.trie 3600).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3598)) := by decide +kernel
theorem s3601 :
    (PathTrie.nthSite PA194.SourceTree.trie 3601).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3594)) := by decide +kernel
theorem s3602 :
    (PathTrie.nthSite PA194.SourceTree.trie 3602).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 7 (some 3605) (some 3603)) := by decide +kernel
theorem s3603 :
    (PathTrie.nthSite PA194.SourceTree.trie 3603).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 2 (some 3604)) := by decide +kernel
theorem s3604 :
    (PathTrie.nthSite PA194.SourceTree.trie 3604).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3602)) := by decide +kernel
theorem s3605 :
    (PathTrie.nthSite PA194.SourceTree.trie 3605).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 1 (some 3609) (some 3606)) := by decide +kernel
theorem s3606 :
    (PathTrie.nthSite PA194.SourceTree.trie 3606).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 7 (some 3607)) := by decide +kernel
theorem s3607 :
    (PathTrie.nthSite PA194.SourceTree.trie 3607).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 6 (some 3608)) := by decide +kernel
theorem s3608 :
    (PathTrie.nthSite PA194.SourceTree.trie 3608).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3605)) := by decide +kernel
theorem s3609 :
    (PathTrie.nthSite PA194.SourceTree.trie 3609).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 6 (some 3615) (some 3610)) := by decide +kernel
theorem s3610 :
    (PathTrie.nthSite PA194.SourceTree.trie 3610).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 7 (some 3611)) := by decide +kernel
theorem s3611 :
    (PathTrie.nthSite PA194.SourceTree.trie 3611).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 6 (some 3614) (some 3612)) := by decide +kernel
theorem s3612 :
    (PathTrie.nthSite PA194.SourceTree.trie 3612).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 1 (some 3613)) := by decide +kernel
theorem s3613 :
    (PathTrie.nthSite PA194.SourceTree.trie 3613).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3611)) := by decide +kernel
theorem s3614 :
    (PathTrie.nthSite PA194.SourceTree.trie 3614).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3605)) := by decide +kernel
theorem s3615 :
    (PathTrie.nthSite PA194.SourceTree.trie 3615).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 7 (some 3621) (some 3616)) := by decide +kernel
theorem s3616 :
    (PathTrie.nthSite PA194.SourceTree.trie 3616).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 1 (some 3617)) := by decide +kernel
theorem s3617 :
    (PathTrie.nthSite PA194.SourceTree.trie 3617).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 1 (some 3618)) := by decide +kernel
theorem s3618 :
    (PathTrie.nthSite PA194.SourceTree.trie 3618).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 1 (some 3619)) := by decide +kernel
theorem s3619 :
    (PathTrie.nthSite PA194.SourceTree.trie 3619).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 1 (some 3620)) := by decide +kernel
theorem s3620 :
    (PathTrie.nthSite PA194.SourceTree.trie 3620).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3615)) := by decide +kernel
#print axioms s3594
#print axioms s3620
end PA194MPLiteralRows
