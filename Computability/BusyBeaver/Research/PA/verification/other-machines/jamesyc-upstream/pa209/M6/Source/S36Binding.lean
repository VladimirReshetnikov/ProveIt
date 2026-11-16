module
public import M6.Source.TrieResolver
public import M6.Source.S36Drain
@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 50000

/-! Kernel-checked control-flow extraction for the exact S36 pre-guard fragment.
This proves a finite source binding, not the semantics of the complete program. -/
namespace M6.Source

/-- The resolved ten instructions at source ordinals 3911 through 3920. -/
def s36Expected : Array Instruction := #[
  .dec 1 (some 3914) (some 3912),
  .inc 6 (some 3913),
  .jump (some 3911),
  .dec 5 (some 3918) (some 3915),
  .inc 1 (some 3916),
  .inc 6 (some 3917),
  .jump (some 3914),
  .dec 6 (some 3921) (some 3919),
  .inc 5 (some 3920),
  .jump (some 3918)
]

theorem s36_resolved_fragment :
    (List.range 10).map (fun j => resolveAt exactSites (3911 + j)) =
      s36Expected.toList.map some := by
  simp only [← PathTrie.fastResolveAt_eq]
  decide +kernel

/-- Individual instruction access follows from the single checked window. -/
theorem s36_resolved_at (j : Fin 10) :
    resolveAt exactSites (3911 + j.val) = some s36Expected[j.val] := by
  have h := congrArg (fun xs => xs[j.val]?) s36_resolved_fragment
  have hj : j.val < s36Expected.size := j.isLt
  simpa only [List.getElem?_map, List.getElem?_range j.isLt, Option.map_some,
    Array.getElem?_toList, Array.getElem?_eq_getElem hj, Option.some.injEq] using h

#print axioms s36_resolved_fragment
end M6.Source

