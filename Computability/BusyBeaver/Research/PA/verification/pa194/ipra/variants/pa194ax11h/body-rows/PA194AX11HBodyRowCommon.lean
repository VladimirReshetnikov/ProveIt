import PA194AX11HBodyCopy
import PA194AX11HGateBinding
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194AX11HBodyRowCommon
open PA194AX11HBodyCopy

def oldChunk (start count : Nat) : List (Option M6.Source.Instruction) :=
  (List.range count).map (fun i => (M6.Source.PathTrie.nthSite PA194.SourceTree.trie (start+i)).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie))
def newChunk (start count : Nat) : List (Option M6.Source.Instruction) :=
  (PA194AX11HSource.program.drop start).take count

theorem chunkRow (start count i : Nat) (hbound : start+count ≤ 3671) (hi : i < count)
    (h : newChunk start count = oldChunk start count) :
    PA194AX11HSource.program[start+i]'(by rw [PA194AX11HSource.program_length]; omega) =
      ((M6.Source.PathTrie.nthSite PA194.SourceTree.trie (start+i)).bind
        (M6.FastResolve.resolveTree PA194.SourceTree.trie)) := by
  have hh := congrArg (fun xs => xs[i]?) h
  simpa [newChunk,oldChunk,hi,PA194AX11HSource.program_length,show start+i < 3671 by omega] using hh
#print axioms chunkRow
end PA194AX11HBodyRowCommon
