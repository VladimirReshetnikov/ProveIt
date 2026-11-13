module
public import PA196.Program
/-! Arithmetic proof adapted from M6.Source.FetchPrefixBinding; every literal
source binding is reproved against the PA196 program. -/
@[expose] public section
set_option maxHeartbeats 2000000
set_option maxRecDepth 50000
namespace PA196.Source
open M6.Source

def fetchPrefixExpected : Array Instruction := #[
  .dec 8 (some 27) (some 26), .jump (some 34),
  .dec 0 (some 31) (some 28), .inc 8 (some 29), .inc 6 (some 30),
  .jump (some 27), .inc 0 (some 32), .dec 6 (some 34) (some 33), .jump (some 31)
]

theorem fetch_prefix_fragment :
    (List.range 9).map (fun j => resolveAt Program.sites (25+j)) = fetchPrefixExpected.toList.map some := by
  simp only [Program.resolve_tree]
  decide +kernel

theorem fetch_prefix_at (j : Fin 9) :
    resolveAt Program.sites (25+j.val) = some fetchPrefixExpected[j.val] := by
  have h := congrArg (fun xs => xs[j.val]?) fetch_prefix_fragment
  have hj : j.val < fetchPrefixExpected.size := j.isLt
  simpa only [List.getElem?_map, List.getElem?_range j.isLt, Option.map_some,
    Array.getElem?_toList, Array.getElem?_eq_getElem hj, Option.some.injEq] using h
end PA196.Source

