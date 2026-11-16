module
public import M6.Source.ExactSource
@[expose] public section
set_option maxHeartbeats 16000000
set_option maxRecDepth 50000

namespace M6.Source

/-- The exact fetch decoder and cleanup, ordinals 9 through 22. -/
def fetchUnpairExpected : Array Instruction := #[
  .dec 8 (some 17) (some 10),
  .inc 7 (some 11),
  .dec 6 (some 13) (some 12),
  .jump (some 16),
  .dec 7 (some 16) (some 14),
  .inc 6 (some 15),
  .jump (some 13),
  .jump (some 9),
  .dec 7 (some 20) (some 18),
  .inc 8 (some 19),
  .jump (some 17),
  .dec 6 (some 23) (some 21),
  .inc 3 (some 22),
  .jump (some 20)
]

theorem fetch_unpair_resolved_fragment :
    (List.range 14).map (fun j => resolveAt exactSites (9+j)) =
      fetchUnpairExpected.toList.map some := by decide

theorem fetch_unpair_resolved_at (j : Fin 14) :
    resolveAt exactSites (9+j.val) = some fetchUnpairExpected[j.val] := by
  have h := congrArg (fun xs => xs[j.val]?) fetch_unpair_resolved_fragment
  have hj : j.val < fetchUnpairExpected.size := j.isLt
  simpa only [List.getElem?_map, List.getElem?_range j.isLt, Option.map_some,
    Array.getElem?_toList, Array.getElem?_eq_getElem hj, Option.some.injEq] using h

#print axioms fetch_unpair_resolved_fragment
end M6.Source

