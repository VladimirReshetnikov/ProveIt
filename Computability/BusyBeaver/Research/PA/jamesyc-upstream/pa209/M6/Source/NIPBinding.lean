module
public import M6.Source.TrieResolver
@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 50000

namespace M6.Source

/-- NIP's guard and cleanup, before Cantor-stack decoding begins at 3933. -/
def nipExpected : Array Instruction := #[
  .inc 6 (some 3922),
  .dec 5 (some 3926) (some 3923),
  .dec 6 (some 3925) (some 3924),
  .jump (some 3922),
  .jump (some 3927),
  .dec 6 (some 3932) (some 3927),
  .dec 5 (some 3929) (some 3928),
  .jump (some 3927),
  .dec 6 (some 3931) (some 3930),
  .jump (some 3927),
  .jump (some 3933),
  .halt
]

theorem nip_resolved_fragment :
    (List.range 12).map (fun j => resolveAt exactSites (3921 + j)) =
      nipExpected.toList.map some := by
  simp only [← PathTrie.fastResolveAt_eq]
  decide +kernel

theorem nip_resolved_at (j : Fin 12) :
    resolveAt exactSites (3921 + j.val) = some nipExpected[j.val] := by
  have h := congrArg (fun xs => xs[j.val]?) nip_resolved_fragment
  have hj : j.val < nipExpected.size := j.isLt
  simpa only [List.getElem?_map, List.getElem?_range j.isLt, Option.map_some,
    Array.getElem?_toList, Array.getElem?_eq_getElem hj, Option.some.injEq] using h

#print axioms nip_resolved_fragment
end M6.Source

