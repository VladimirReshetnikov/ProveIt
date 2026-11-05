import FreshModel106
import DiophantineConsistency.ArithmeticMaskData

/-! Canonical base-256 bytes of the independent six-run low-mask recipe. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.CurrentMCBytes

def rho : ℕ := 2^47

/-- Little-endian base-2^47 mask digits. -/
def maskDigits : List ℕ :=
  List.replicate 951 (rho-2) ++ (List.replicate 9 (rho-1) ++
    (List.replicate 26 (rho-2) ++ (List.replicate 18 (rho-1) ++
      (List.replicate 1 (rho-2) ++ (List.replicate 1006 (rho-1) ++ [])))))

theorem rho_eq : rho = CurrentMasks2011.radix := rfl

theorem maskDigits_eq : maskDigits = ArithmeticMaskData.lowDigits := by
  unfold maskDigits ArithmeticMaskData.lowDigits ArithmeticMaskData.lowList
  simp only [ArithmeticMaskData.radix_pred]
  rfl

attribute [local irreducible] rho maskDigits CurrentMasks2011.radix CurrentMasks2011.lowPort

/-- Canonical big-endian base-256 conversion of the explicit digit recipe. -/
def bigBytes : List ℕ := (Nat.digits 256 (Nat.ofDigits rho maskDigits)).reverse

theorem decode_mc :
    (Nat.ofDigits 256 bigBytes.reverse : ℤ) = CurrentWindowCarry2011.ports 2 := by
  rw [bigBytes, List.reverse_reverse]
  calc
    (Nat.ofDigits 256 (Nat.digits 256 (Nat.ofDigits rho maskDigits)) : ℤ) =
        (Nat.ofDigits rho maskDigits : ℤ) :=
      congrArg (fun n : ℕ => (n : ℤ)) (Nat.ofDigits_digits 256 (Nat.ofDigits rho maskDigits))
    _ = (CurrentMasks2011.lowPort : ℤ) := by
      rw [ArithmeticMaskData.lowPort_ofDigits, ← maskDigits_eq, ← rho_eq]
      rfl

#print axioms decode_mc
end DiophantineConsistency.CurrentMCBytes
