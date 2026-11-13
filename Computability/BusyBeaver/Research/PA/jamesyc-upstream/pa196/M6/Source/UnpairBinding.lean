module
public import M6.Source.TrieResolver
@[expose] public section
set_option maxHeartbeats 16000000
set_option maxRecDepth 50000

namespace M6.Source

/-- The exact stack decoder and cleanup, ordinals 3933 through 3946. -/
def unpairExpected : Array Instruction := #[
  .dec 2 (some 3941) (some 3934),
  .inc 7 (some 3935),
  .dec 6 (some 3937) (some 3936),
  .jump (some 3940),
  .dec 7 (some 3940) (some 3938),
  .inc 6 (some 3939),
  .jump (some 3937),
  .jump (some 3933),
  .dec 7 (some 3944) (some 3942),
  .inc 2 (some 3943),
  .jump (some 3941),
  .dec 6 none (some 3945),
  .inc 5 (some 3946),
  .jump (some 3944)
]

theorem unpair_resolved_fragment :
    (List.range 14).map (fun j => resolveAt exactSites (3933+j)) =
      unpairExpected.toList.map some := by
  simp only [← PathTrie.fastResolveAt_eq]
  decide +kernel

theorem unpair_resolved_at (j : Fin 14) :
    resolveAt exactSites (3933+j.val) = some unpairExpected[j.val] := by
  have h := congrArg (fun xs => xs[j.val]?) unpair_resolved_fragment
  have hj : j.val < unpairExpected.size := j.isLt
  simpa only [List.getElem?_map, List.getElem?_range j.isLt, Option.map_some,
    Array.getElem?_toList, Array.getElem?_eq_getElem hj, Option.some.injEq] using h

#print axioms unpair_resolved_fragment
end M6.Source

