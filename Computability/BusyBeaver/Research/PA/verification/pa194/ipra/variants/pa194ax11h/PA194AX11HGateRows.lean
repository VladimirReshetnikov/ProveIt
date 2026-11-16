import PA194AX11HSource
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194AX11HGateRows

def oldGate : List (Option M6.Source.Instruction) :=
  (List.range 34).map (fun i => (M6.Source.PathTrie.nthSite PA194.SourceTree.trie (3519+i)).bind
    (M6.FastResolve.resolveTree PA194.SourceTree.trie))

def newGate : List (Option M6.Source.Instruction) := (PA194AX11HSource.program.drop 3519).take 34

/-- The entire unchanged 34-site AX gate window, checked against the primary trie. -/
theorem same_gate_rows : newGate = oldGate := by decide +kernel

#print axioms same_gate_rows
end PA194AX11HGateRows
