import PA194SourceProgram
import M6.Source.S36Drain
/-! Arithmetic proof adapted from M6.Source.S36Binding; every literal
source binding is reproved against the PA194 program. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 50000

/-! Kernel-checked control-flow extraction for the exact S36 pre-guard fragment.
This proves a finite source binding, not the semantics of the complete program. -/
namespace PA194ShiftSource
open M6.Source

/-- The resolved ten instructions at source ordinals 3661 through 3670. -/
def s36Expected : Array Instruction := #[
  .dec 1 (some 3664) (some 3662),
  .inc 6 (some 3663),
  .jump (some 3661),
  .dec 5 (some 3668) (some 3665),
  .inc 1 (some 3666),
  .inc 6 (some 3667),
  .jump (some 3664),
  .dec 6 (some 3671) (some 3669),
  .inc 5 (some 3670),
  .jump (some 3668)
]

theorem s36_resolved_fragment :
    (List.range 10).map (fun j => resolveAt PA194SourceProgram.sites (3661 + j)) =
      s36Expected.toList.map some := by
  simp only [PA194SourceProgram.resolve_tree]
  decide +kernel

/-- Individual instruction access follows from the single checked window. -/
theorem s36_resolved_at (j : Fin 10) :
    resolveAt PA194SourceProgram.sites (3661 + j.val) = some s36Expected[j.val] := by
  have h := congrArg (fun xs => xs[j.val]?) s36_resolved_fragment
  have hj : j.val < s36Expected.size := j.isLt
  simpa only [List.getElem?_map, List.getElem?_range j.isLt, Option.map_some,
    Array.getElem?_toList, Array.getElem?_eq_getElem hj, Option.some.injEq] using h

#print axioms s36_resolved_fragment
end PA194ShiftSource

