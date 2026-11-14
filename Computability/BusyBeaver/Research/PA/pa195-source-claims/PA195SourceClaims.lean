import PA195SourceTree
set_option autoImplicit false
namespace PA195SourceClaims
open M6.Source M6.Source.PathTrie M6.FastResolve PA195.SourceTree

structure Claim where
  ordinal : Nat
  site : Site
  instruction : Instruction
  deriving DecidableEq, Repr

def accepted (c : Claim) : Bool :=
  (nthSite trie c.ordinal == some c.site) &&
  (resolveTree trie c.site == some c.instruction)

/-- A checked claim agrees with both the actual flattened source tree and
its original source control-flow resolver. -/
theorem accepted_sound (c : Claim) (h : accepted c = true) :
    (flatten trie)[c.ordinal]? = some c.site ∧
    resolveAt (flatten trie).toArray c.ordinal = some c.instruction := by
  have hs : nthSite trie c.ordinal = some c.site ∧
      resolveTree trie c.site = some c.instruction := by
    simpa [accepted, Bool.and_eq_true, beq_iff_eq] using h
  constructor
  · simpa [nthSite_eq] using hs.1
  · have hidx : ((flatten trie).toArray)[c.ordinal]? = some c.site := by
      simpa [nthSite_eq] using hs.1
    have heq : resolveTree trie c.site = resolve (flatten trie).toArray c.site :=
      resolveTree_eq trie (flatten trie).toArray (by simp) c.site
    simp [resolveAt, hidx, ← heq, hs.2]

#print axioms accepted_sound
end PA195SourceClaims
