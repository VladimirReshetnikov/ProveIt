module
public import M6.Legacy213.FastResolve
public import M6.Legacy213.SourceSites
public import M6.Legacy213.SourceTrie
public import M6.Legacy213.SourceCodes
public import M6.Source.ExactTrie
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000
namespace M6.Legacy213.SourceProgram
open M6.Source M6.Source.PathTrie M6.Legacy213.FastResolve
def path (i : Nat) : Path := ((sites[i]?).map (·.path)).getD []
theorem sites_count : sites.size = 3947 := by decide +kernel
theorem codes_count : codes.size = 3947 := by decide +kernel
end M6.Legacy213.SourceProgram
