import PA194SourceProgram
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194SourceHaltSite
open M6.Source M6.Source.PathTrie PA194.SourceTree PA194SourceProgram

def haltSite : Site := ⟨[false,false,true], .halt⟩
theorem haltSiteAt10 : nthSite trie 10 = some haltSite := by decide +kernel
theorem haltSiteResolves : M6.FastResolve.resolveTree trie haltSite = some .halt := by decide +kernel
theorem uniqueHaltLeaf : sites.toList.filter (fun s => s.op == .halt) = [haltSite] := by decide +kernel
#print axioms haltSiteAt10
#print axioms haltSiteResolves
#print axioms uniqueHaltLeaf
end PA194SourceHaltSite
