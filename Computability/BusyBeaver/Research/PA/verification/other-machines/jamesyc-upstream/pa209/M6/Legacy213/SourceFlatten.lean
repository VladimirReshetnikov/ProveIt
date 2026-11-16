module
public import M6.Legacy213.SourceProgramData
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000
namespace M6.Legacy213.SourceProgram
open M6.Source M6.Source.PathTrie
theorem flatten_exact : flatten trie = sites.toList := by decide +kernel
end M6.Legacy213.SourceProgram
