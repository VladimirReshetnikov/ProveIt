import PA194SourceTree
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194AXSource
open M6.Source M6.Source.PathTrie PA194.SourceTree

inductive Token where
 | push | copyD | copyH | copyA | cons | incT | readH | readDCons
 | copyGuard | compareGuard | close
 deriving DecidableEq, Repr

def tokenTree : Token → Tree
 | .push => node49
 | .copyD => node55
 | .copyH => node58
 | .copyA => node70
 | .cons => node65
 | .incT => .leaf (.inc 1)
 | .readH => node72
 | .readDCons => node75
 | .copyGuard => node142
 | .compareGuard => node150
 | .close => .leaf (.breakTo 1)

def rawLeaves : Tree → List M6.Source.Op
 | .leaf op => [op]
 | .node l r => rawLeaves l ++ rawLeaves r

def tokens : List Token := [
.copyH, .copyD, .cons, .incT, .incT, .readH, .copyH, .copyD, .cons, .readDCons, .copyD, .copyH, .cons, .copyA, .copyH, .cons, .cons, .cons, .copyH, .copyD, .cons, .incT, .incT, .push, .incT, .cons, .copyD, .cons, .incT, .incT, .push, .incT, .cons, .copyH, .cons, .copyH, .copyA, .cons, .incT, .incT, .copyD, .cons, .incT, .incT, .copyH, .copyD, .cons, .incT, .incT, .copyA, .cons, .incT, .incT, .cons, .copyH, .copyD, .cons, .incT, .copyH, .copyA, .cons, .incT, .incT, .incT, .copyA, .copyD, .cons, .incT, .cons, .cons, .copyH, .copyD, .cons, .incT, .incT, .incT, .copyA, .copyH, .cons, .incT, .copyA, .copyD, .cons, .incT, .cons, .cons, .copyH, .copyD, .cons, .incT, .incT, .incT, .push, .incT, .cons, .copyD, .cons, .incT, .incT, .push, .incT, .cons, .copyA, .copyD, .cons, .incT, .incT, .copyA, .copyH, .cons, .copyD, .cons, .incT, .incT, .copyH, .copyD, .cons, .incT, .incT, .cons, .cons, .copyA, .copyA, .copyA, .cons, .incT, .incT, .cons, .copyH, .copyD, .cons, .incT, .copyH, .copyD, .cons, .incT, .copyA, .cons, .incT, .incT, .cons, .copyH, .copyD, .cons, .incT, .copyA, .copyA, .copyD, .cons, .incT, .cons, .cons, .copyA, .copyD, .cons, .incT, .copyA, .cons, .push, .incT, .cons, .cons, .push, .incT, .cons, .copyD, .cons, .incT, .incT, .copyA, .copyA, .copyD, .cons, .incT, .cons, .push, .incT, .cons, .cons, .copyA, .cons, .incT, .incT, .cons, .push, .incT, .cons, .copyGuard, .compareGuard, .close]

theorem token_count : tokens.length = 190 := by decide +kernel

theorem exact_raw_source : rawLeaves x67 = tokens.flatMap (rawLeaves ∘ tokenTree) := by
  decide +kernel

#print axioms token_count
#print axioms exact_raw_source
end PA194AXSource
