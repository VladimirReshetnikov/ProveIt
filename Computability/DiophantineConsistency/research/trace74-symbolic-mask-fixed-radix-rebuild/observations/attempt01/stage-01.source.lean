import Trace74GenericDefect
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74FixedRadix
open Finset CompactListMask
open scoped BigOperators

/-- Fix only the radix; keep lengths, index and support symbolic. -/
theorem low_add_defect (short long special : ℕ) (S : Finset ℕ)
    (hlen : short ≤ long) (hspecial : special < short)
    (hsupport : S ⊆ Finset.range short) :
    Nat.ofDigits (2^67) (digits (2^67) long special S) +
      Nat.ofDigits (2^67) ((List.range short).map (defect special S)) + 1 =
        (2^67)^long := by
  exact Trace74GenericDefect.low_add_defect (2^67) short long special S
    (by norm_num) hlen hspecial hsupport

#print axioms Trace74FixedRadix.low_add_defect
end Trace74FixedRadix
