import DiophantineConsistency.MFCurrentKernel2011
import DiophantineConsistency.MFWangTiles942PhysicalOrder

/-! Independent physical-order recipe for the current2011 kernel. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiophantineConsistency.CurrentKernelBytes
open scoped BigOperators
open CurrentKernel2011
open MF.WangTiles942PhysicalOrder

def recipe (r : ℕ) : ℕ :=
  r ^ 18 + r ^ 1004 + r ^ 2020 +
    ((∑ p : Fin 942, 2 * weightAt p * r ^ (1005 - p.val)) +
     ((∑ j : Fin 8, 2 * 2 ^ (10 + j.val) * r ^ (1005 - (978 + j.val))) +
     ((∑ j : Fin 9, 2 * 2 ^ (18 + j.val) * r ^ (1005 - (960 + j.val))) +
     ((∑ j : Fin 8, 2 * 2 ^ (27 + j.val) * r ^ (1005 - (969 + j.val))) +
      (∑ j : Fin 9, 2 * 2 ^ (35 + j.val) * r ^ (1005 - (942 + j.val)))))))

theorem rawWord_recipe (r : ℕ) : CurrentKernel2011.rawWord r = recipe r := by
  rw [MF.CurrentKernel2011.rawWord_eq]
  unfold recipe
  simp only [Fintype.sum_sum_type, CurrentKernel2011.position, CurrentKernel2011.weight]
  rw [selector_sum_reindex (fun pos weight => 2 * weight * r ^ (1005 - pos))]

attribute [local irreducible] recipe CurrentKernel2011.rawWord

theorem recipe_eq_kernel : recipe (2 ^ 47) = CurrentKernel2011.K := by
  change recipe (2 ^ 47) = CurrentKernel2011.rawWord (2 ^ 47)
  exact (rawWord_recipe (2 ^ 47)).symm

theorem kernel_port : (CurrentKernel2011.K : ℤ) = CurrentWindowCarry2011.ports 1 := by
  rfl

attribute [local irreducible] CurrentKernel2011.K CurrentWindowCarry2011.ports

/-- Canonical big-endian bytes of the physical-order kernel recipe. -/
def bigBytes : List ℕ := (Nat.digits 256 (recipe (2 ^ 47))).reverse

theorem decode_kernel :
    ((Nat.ofDigits 256 ((Nat.digits 256 (recipe (2 ^ 47))).reverse).reverse : ℕ) : ℤ) =
      CurrentWindowCarry2011.ports 1 := by
  calc
    _ = ((Nat.ofDigits 256 (Nat.digits 256 (recipe (2 ^ 47))) : ℕ) : ℤ) :=
      congrArg (fun xs : List ℕ => ((Nat.ofDigits 256 xs : ℕ) : ℤ))
        (List.reverse_reverse _)
    _ = (recipe (2 ^ 47) : ℤ) :=
      congrArg (fun n : ℕ => (n : ℤ)) (Nat.ofDigits_digits 256 _)
    _ = (CurrentKernel2011.K : ℤ) := congrArg (fun n : ℕ => (n : ℤ)) recipe_eq_kernel
    _ = CurrentWindowCarry2011.ports 1 := kernel_port

#print axioms rawWord_recipe
#print axioms recipe_eq_kernel
#print axioms kernel_port
#print axioms decode_kernel
end DiophantineConsistency.CurrentKernelBytes
