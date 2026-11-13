module
public import PA196.Program
public import M6.Source.S36Drain
/-! Arithmetic proof adapted from M6.Source.S36Binding; every literal
source binding is reproved against the PA196 program. -/
@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 50000

/-! Kernel-checked control-flow extraction for the exact S36 pre-guard fragment.
This proves a finite source binding, not the semantics of the complete program. -/
namespace PA196.Source
open M6.Source

/-- The resolved ten instructions at source ordinals 3800 through 3809. -/
def s36Expected : Array Instruction := #[
  .dec 1 (some 3803) (some 3801),
  .inc 6 (some 3802),
  .jump (some 3800),
  .dec 5 (some 3807) (some 3804),
  .inc 1 (some 3805),
  .inc 6 (some 3806),
  .jump (some 3803),
  .dec 6 (some 3810) (some 3808),
  .inc 5 (some 3809),
  .jump (some 3807)
]

theorem s36_resolved_fragment :
    (List.range 10).map (fun j => resolveAt Program.sites (3800 + j)) =
      s36Expected.toList.map some := by
  simp only [Program.resolve_tree]
  decide +kernel

/-- Individual instruction access follows from the single checked window. -/
theorem s36_resolved_at (j : Fin 10) :
    resolveAt Program.sites (3800 + j.val) = some s36Expected[j.val] := by
  have h := congrArg (fun xs => xs[j.val]?) s36_resolved_fragment
  have hj : j.val < s36Expected.size := j.isLt
  simpa only [List.getElem?_map, List.getElem?_range j.isLt, Option.map_some,
    Array.getElem?_toList, Array.getElem?_eq_getElem hj, Option.some.injEq] using h

#print axioms s36_resolved_fragment
end PA196.Source

