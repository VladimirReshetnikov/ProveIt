import DiophantineConsistency.CompactSymbolicKernelOpaque
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSymbolicKernelOldShape
open CompactSymbolicKernel CompactSymbolicKernelOpaque
open scoped BigOperators

def bareAt (r : ℕ) : ℕ := r^30+r^62+r^1100+r^2201
def reflectedAt (r e c : ℕ) : ℕ := c*(r^(4393-e)+r^(5495-e))
def selectorAt (r : ℕ) : ℕ := ∑ i : Fin 943, reflectedAt r i.val (CompactCoefficientMass.selector (Compact943Data.row i))
def copyAt (r : ℕ) : ℕ := ∑ i : Fin 41, reflectedAt r (position i) (2^(10+i.val))
def oldAt (r : ℕ) : ℕ := bareAt r+selectorAt r+copyAt r+(r^8807)*r^42

theorem oldAt_eq_param (r : ℕ) : oldAt r = paramKernel r := by rfl
#print axioms CompactSymbolicKernelOldShape.oldAt_eq_param
end CompactSymbolicKernelOldShape
