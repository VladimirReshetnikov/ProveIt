import PA195SourceTree
import PA195Site25

/-! The generated PA195 source tree, its entry instruction, and both concrete
physical branches. The generator's pinned upstream-program and grammar input
are the explicit source-generation boundary. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option autoImplicit false
namespace PA195SourceEntry
open M6.Source M6.Source.PathTrie M6.FastResolve PA195.SourceTree
open M6.Zip M6.Runtime PA195RuntimeEngine PA195Site25

def entrySite : Site := ⟨[true,false,false,false,false,false], .dec 8⟩
def positiveSite : Site := ⟨[true,false,false,false,false,true], .breakTo 1⟩
def zeroSite : Site := ⟨[true,false,false,false,true,false,false], .dec 0⟩

theorem entry_site : nthSite trie 25 = some entrySite := by decide +kernel

theorem entry_instruction : resolveTree trie entrySite = some (.dec 8 (some 27) (some 26)) := by decide +kernel

theorem positive_site : nthSite trie 26 = some positiveSite := by decide +kernel

theorem zero_site : nthSite trie 27 = some zeroSite := by decide +kernel

/-- The two resolved successors of source entry 25 have exact positive
physical realizations, for every gap and every valid full register file. -/
theorem entry_tree_physical (n : Nat) (vs : List Nat) (hlen : 10 ≤ vs.length) :
    (vs.getD 1 0 = 0 → Reach1 machine (conc n vs entry) (conc n vs zeroTarget)) ∧
    (vs.getD 1 0 ≠ 0 → Reach1 machine (conc n vs entry) (conc n vs positiveTarget)) := by
  constructor
  · intro hz
    exact zero_reach n vs ⟨hlen, hz⟩
  · intro hp
    exact positive_reach n vs ⟨hlen, hp⟩

/-- The exact formal source entry and both symbolic physical branch contracts
are packaged together for every valid complete register file. -/
theorem entry_binding :
    nthSite trie 25 = some entrySite ∧
    resolveTree trie entrySite = some (.dec 8 (some 27) (some 26)) ∧
    nthSite trie 26 = some positiveSite ∧
    nthSite trie 27 = some zeroSite ∧
    ∀ n vs, 10 ≤ vs.length →
      (vs.getD 1 0 = 0 → Reach1 machine (conc n vs entry) (conc n vs zeroTarget)) ∧
      (vs.getD 1 0 ≠ 0 → Reach1 machine (conc n vs entry) (conc n vs positiveTarget)) :=
  ⟨entry_site, entry_instruction, positive_site, zero_site, entry_tree_physical⟩

#print axioms entry_binding
#print axioms entry_site
#print axioms entry_instruction
#print axioms positive_site
#print axioms zero_site
#print axioms entry_tree_physical
end PA195SourceEntry
