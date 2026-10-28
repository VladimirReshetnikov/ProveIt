import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeSupply
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionFinalTheorems

namespace OAI.Algorithms

/-! Closed fixed-machine endpoints. The concrete mass and accepted-count
programs, their actual histories, and all native costs are supplied here. -/
namespace SubexponentialSAT.SqrtLog.Execution.Final
open SubexponentialSAT BitProgram StructuredCalls
noncomputable section

 theorem nativeServices_exists (width : ℕ) (hw : 3 ≤ width) :
    Nonempty (NativeServices width) := by
  obtain ⟨T,hT⟩ := SparsificationBudgetProgram.exists_control width
  let c := finalConfig width T (by omega) hT
  have hc : 896 < SubexpSetupProgram.helperSize c := finalConfig_leaf_fits width T (by omega) hT
  obtain ⟨qi,hqi⟩ := occurrence_power c
  obtain ⟨Ct,At,dt,hCt,hAt,hdt,hservice⟩ := OuterNativeServices.exists_sparse_history width qi
  exact ⟨{
    config := c, width_eq := rfl, fits := hc,
    mass := LeafOuterNative.mass width, acceptedCount := LeafOuterNative.acceptedCount width,
    tailConstant := Ct, tailExponent := At, degree := dt,
    constant_ge := hCt, exponent_nonneg := hAt, degree_pos := hdt,
    measured := observedHistoryContract_of_sparse c _ _ Ct At dt qi hqi hservice
  }⟩

 theorem mainTheorem : Statement.MainTheorem := mainTheorem_of_services nativeServices_exists
 theorem binaryIdentifierMainTheorem : Statement.BinaryIdentifierMainTheorem :=
  binaryIdentifierMainTheorem_of_services nativeServices_exists
 theorem fullMainTheorem : Statement.FullMainTheorem := fullMainTheorem_of_services nativeServices_exists

end
end SubexponentialSAT.SqrtLog.Execution.Final

end OAI.Algorithms
