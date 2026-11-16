module
public import M6.Source.ExactSource
@[expose] public section
set_option maxHeartbeats 2000000
set_option maxRecDepth 50000
namespace M6.Source

def fetchPrefixExpected : Array Instruction := #[
  .dec 8 (some 2) (some 1), .jump (some 9),
  .dec 0 (some 6) (some 3), .inc 8 (some 4), .inc 6 (some 5),
  .jump (some 2), .inc 0 (some 7), .dec 6 (some 9) (some 8), .jump (some 6)
]

theorem fetch_prefix_fragment :
    (List.range 9).map (resolveAt exactSites) = fetchPrefixExpected.toList.map some := by decide

theorem fetch_prefix_at (j : Fin 9) :
    resolveAt exactSites j.val = some fetchPrefixExpected[j.val] := by
  have h := congrArg (fun xs => xs[j.val]?) fetch_prefix_fragment
  have hj : j.val < fetchPrefixExpected.size := j.isLt
  simpa only [List.getElem?_map, List.getElem?_range j.isLt, Option.map_some,
    Array.getElem?_toList, Array.getElem?_eq_getElem hj, Option.some.injEq] using h
end M6.Source

