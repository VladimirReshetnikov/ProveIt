import PA194SourceTree

/-! Concrete facts about the generated PA194 source tree. The source program
and grammar are pinned by the generator; this is not a consistency theorem. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194SourceFacts
open M6.Source M6.Source.PathTrie M6.FastResolve PA194.SourceTree

def branchCount : Tree → Nat
  | .leaf (.dec _) => 2
  | .leaf _ => 1
  | .node l r => branchCount l + branchCount r

def entry : Site := ⟨[true,false,false,false,false,false], .dec 8⟩

theorem site_count : size trie = 3673 := by decide +kernel

theorem branch_count : branchCount trie = 4780 := by decide +kernel

theorem entry_site : nthSite trie 25 = some entry := by decide +kernel

theorem entry_instruction : resolveTree trie entry = some (.dec 8 (some 27) (some 26)) := by decide +kernel

theorem continue_two_lookup :
    lookup trie [true,false,true,true,true,true,true,true] = some 3670 := by decide +kernel

theorem continue_two_site :
    nthSite trie 3670 = some ⟨[true,false,true,true,true,true,true,true], .continueTo 2⟩ := by decide +kernel

theorem decrement_six_lookup :
    lookup trie [true,false,true,true,true,true,false] = some 3668 := by decide +kernel

theorem decrement_six_site :
    nthSite trie 3668 = some ⟨[true,false,true,true,true,true,false], .dec 6⟩ := by decide +kernel

theorem continue_two_instruction :
    resolveTree trie ⟨[true,false,true,true,true,true,true,true], .continueTo 2⟩ =
      some (.jump (some 3668)) := by decide +kernel

theorem decrement_six_instruction :
    resolveTree trie ⟨[true,false,true,true,true,true,false], .dec 6⟩ =
      some (.dec 6 (some 3671) (some 3669)) := by decide +kernel

theorem decrement_six_positive_site :
    nthSite trie 3669 = some ⟨[true,false,true,true,true,true,true,false], .inc 5⟩ := by decide +kernel

theorem decrement_six_zero_site :
    nthSite trie 3671 = some ⟨[true,true,false], .inc 6⟩ := by decide +kernel

#print axioms site_count
#print axioms branch_count
#print axioms entry_site
#print axioms entry_instruction
#print axioms continue_two_lookup
#print axioms continue_two_site
#print axioms decrement_six_lookup
#print axioms decrement_six_site
#print axioms continue_two_instruction
#print axioms decrement_six_instruction
#print axioms decrement_six_positive_site
#print axioms decrement_six_zero_site
end PA194SourceFacts
