import PA194SourceProgram

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194AXGateRows
open M6.Source

theorem s3519 :
    (PathTrie.nthSite PA194.SourceTree.trie 3519).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 3 (some 3523) (some 3520)) := by decide +kernel

theorem s3520 :
    (PathTrie.nthSite PA194.SourceTree.trie 3520).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 7 (some 3521)) := by decide +kernel

theorem s3521 :
    (PathTrie.nthSite PA194.SourceTree.trie 3521).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 6 (some 3522)) := by decide +kernel

theorem s3522 :
    (PathTrie.nthSite PA194.SourceTree.trie 3522).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3519)) := by decide +kernel

theorem s3523 :
    (PathTrie.nthSite PA194.SourceTree.trie 3523).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 5 (some 3527) (some 3524)) := by decide +kernel

theorem s3524 :
    (PathTrie.nthSite PA194.SourceTree.trie 3524).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 6 (some 3526) (some 3525)) := by decide +kernel

theorem s3525 :
    (PathTrie.nthSite PA194.SourceTree.trie 3525).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3523)) := by decide +kernel

theorem s3526 :
    (PathTrie.nthSite PA194.SourceTree.trie 3526).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3528)) := by decide +kernel

theorem s3527 :
    (PathTrie.nthSite PA194.SourceTree.trie 3527).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 6 (some 3533) (some 3528)) := by decide +kernel

theorem s3528 :
    (PathTrie.nthSite PA194.SourceTree.trie 3528).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 5 (some 3530) (some 3529)) := by decide +kernel

theorem s3529 :
    (PathTrie.nthSite PA194.SourceTree.trie 3529).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3528)) := by decide +kernel

theorem s3530 :
    (PathTrie.nthSite PA194.SourceTree.trie 3530).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 6 (some 3532) (some 3531)) := by decide +kernel

theorem s3531 :
    (PathTrie.nthSite PA194.SourceTree.trie 3531).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3528)) := by decide +kernel

theorem s3532 :
    (PathTrie.nthSite PA194.SourceTree.trie 3532).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3535)) := by decide +kernel

theorem s3533 :
    (PathTrie.nthSite PA194.SourceTree.trie 3533).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 1 (some 3535) (some 3534)) := by decide +kernel

theorem s3534 :
    (PathTrie.nthSite PA194.SourceTree.trie 3534).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3533)) := by decide +kernel

theorem s3535 :
    (PathTrie.nthSite PA194.SourceTree.trie 3535).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 7 (some 3538) (some 3536)) := by decide +kernel

theorem s3536 :
    (PathTrie.nthSite PA194.SourceTree.trie 3536).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 6 (some 3537)) := by decide +kernel

theorem s3537 :
    (PathTrie.nthSite PA194.SourceTree.trie 3537).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3535)) := by decide +kernel

theorem s3538 :
    (PathTrie.nthSite PA194.SourceTree.trie 3538).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 4 (some 3541) (some 3539)) := by decide +kernel

theorem s3539 :
    (PathTrie.nthSite PA194.SourceTree.trie 3539).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.inc 5 (some 3540)) := by decide +kernel

theorem s3540 :
    (PathTrie.nthSite PA194.SourceTree.trie 3540).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3538)) := by decide +kernel

theorem s3541 :
    (PathTrie.nthSite PA194.SourceTree.trie 3541).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 5 (some 3545) (some 3542)) := by decide +kernel

theorem s3542 :
    (PathTrie.nthSite PA194.SourceTree.trie 3542).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 6 (some 3544) (some 3543)) := by decide +kernel

theorem s3543 :
    (PathTrie.nthSite PA194.SourceTree.trie 3543).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3541)) := by decide +kernel

theorem s3544 :
    (PathTrie.nthSite PA194.SourceTree.trie 3544).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3546)) := by decide +kernel

theorem s3545 :
    (PathTrie.nthSite PA194.SourceTree.trie 3545).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 6 (some 3551) (some 3546)) := by decide +kernel

theorem s3546 :
    (PathTrie.nthSite PA194.SourceTree.trie 3546).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 5 (some 3548) (some 3547)) := by decide +kernel

theorem s3547 :
    (PathTrie.nthSite PA194.SourceTree.trie 3547).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3546)) := by decide +kernel

theorem s3548 :
    (PathTrie.nthSite PA194.SourceTree.trie 3548).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 6 (some 3550) (some 3549)) := by decide +kernel

theorem s3549 :
    (PathTrie.nthSite PA194.SourceTree.trie 3549).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3546)) := by decide +kernel

theorem s3550 :
    (PathTrie.nthSite PA194.SourceTree.trie 3550).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3553)) := by decide +kernel

theorem s3551 :
    (PathTrie.nthSite PA194.SourceTree.trie 3551).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.dec 1 (some 3553) (some 3552)) := by decide +kernel

theorem s3552 :
    (PathTrie.nthSite PA194.SourceTree.trie 3552).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3551)) := by decide +kernel

theorem s3553 :
    (PathTrie.nthSite PA194.SourceTree.trie 3553).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 3660)) := by decide +kernel

theorem s3660 :
    (PathTrie.nthSite PA194.SourceTree.trie 3660).bind
      (M6.FastResolve.resolveTree PA194.SourceTree.trie) = some (.jump (some 25)) := by decide +kernel

#print axioms s3519
#print axioms s3660
end PA194AXGateRows
