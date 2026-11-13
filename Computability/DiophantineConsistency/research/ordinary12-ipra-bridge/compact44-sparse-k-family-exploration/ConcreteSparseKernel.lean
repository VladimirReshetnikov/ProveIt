import AbstractSparseFamily
import DiophantineConsistency.CompactKernelFiniteCert
import DiophantineConsistency.CompactSymbolicKernelOpaque
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ConcreteSparseKernel
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactKernelFiniteCert
open scoped BigOperators

def selectorWeight (i : Fin 943) : ℕ :=
  CompactCoefficientMass.selector (Compact943Data.row i)

def copyWeight (i : Fin 41) : ℕ := 2 ^ (10 + i.val)

def kernelTerms : List (ℕ × ℕ) :=
  [(30,1),(62,1),(1100,1),(2201,1)] ++
  AbstractSparseFamily.twoBands (fun i : Fin 943 => 4393-i.val)
    (fun i => 5495-i.val) selectorWeight ++
  AbstractSparseFamily.twoBands (fun i : Fin 41 => 4393-position i)
    (fun i => 5495-position i) copyWeight ++ [(8849,1)]

theorem kernel_weighted_sum (r : ℕ) :
    paramKernel r = (kernelTerms.map (fun t => t.2 * r ^ t.1)).sum := by
  simp only [kernelTerms, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, one_mul, AbstractSparseFamily.twoBands_weighted_sum,
    paramKernel, selectorWeight, copyWeight]
  rw [show (8849 : ℕ) = 8807 + 42 by decide, pow_add]
  ring

#print axioms ConcreteSparseKernel.kernel_weighted_sum
end ConcreteSparseKernel
