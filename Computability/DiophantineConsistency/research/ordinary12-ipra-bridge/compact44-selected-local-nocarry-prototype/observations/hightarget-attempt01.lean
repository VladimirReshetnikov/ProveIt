import DiophantineConsistency.CompactHighPopulation
import Mathlib.Data.List.GetD
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace HighTargetDigits
open CompactHighPopulation

theorem target4393 : highDigits.getD 4393 0 = mu := by
  simp (disch := omega) only [highDigits,List.getD_append_right,List.getD_append,
    List.length_replicate,List.length_cons,List.length_nil,List.length_append,
    Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,List.getD_cons_zero]

theorem target5495 : highDigits.getD 5495 0 = mu := by
  simp (disch := omega) only [highDigits,List.getD_append_right,List.getD_append,
    List.length_replicate,List.length_cons,List.length_nil,List.length_append,
    Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,List.getD_cons_zero]
#print axioms HighTargetDigits.target4393
#print axioms HighTargetDigits.target5495
end HighTargetDigits
