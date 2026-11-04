import Trace74GenericDefect
import Trace74SupportShort
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74FixedSupport
open Finset CompactListMask CompactConcreteMask
open scoped BigOperators

/-- Fix the support and short length; leave the radix and long length symbolic. -/
theorem low_add_defect (B long special : ℕ) (hB : 4 ≤ B)
    (hlen : 3297 ≤ long) (hspecial : special < 3297) :
    Nat.ofDigits B (digits B long special support) +
      Nat.ofDigits B ((List.range 3297).map (defect special support)) + 1 = B^long := by
  exact Trace74GenericDefect.low_add_defect B 3297 long special support
    hB hlen hspecial Trace74SupportShort.support_short

#print axioms Trace74FixedSupport.low_add_defect
end Trace74FixedSupport
