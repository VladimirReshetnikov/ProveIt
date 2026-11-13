import CurrentMFNaturalSum
import CurrentMFPortCast

/-! Explicit proof-term composition for the same once-shifted byte list. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.CurrentMFDecoderExplicit
open CurrentMFRecipe
attribute [local irreducible] rho maskDigits CurrentMasks2011.radix
  CurrentMasks2011.highPort CurrentMasks2011.beta CurrentWindowCarry2011.ports

def shiftedValue : ℕ := Nat.ofDigits rho maskDigits + (rho ^ 2011 - 1)
def bigBytes : List ℕ := (Nat.digits 256 shiftedValue).reverse

theorem natural_decode :
    (Nat.ofDigits 256 ((Nat.digits 256
      (Nat.ofDigits rho maskDigits + (rho ^ 2011 - 1))).reverse.reverse) : ℕ) =
      CurrentMasks2011.highPort + CurrentMasks2011.beta :=
  (congrArg (Nat.ofDigits 256)
    (List.reverse_reverse (Nat.digits 256 (Nat.ofDigits rho maskDigits + (rho ^ 2011 - 1))))).trans
    ((Nat.ofDigits_digits 256 (Nat.ofDigits rho maskDigits + (rho ^ 2011 - 1))).trans
      CurrentMFNaturalSum.natural_sum)

theorem decode_mf :
    ((Nat.ofDigits 256 ((Nat.digits 256
      (Nat.ofDigits rho maskDigits + (rho ^ 2011 - 1))).reverse.reverse) : ℕ) : ℤ) =
      CurrentWindowCarry2011.ports 3 :=
  (congrArg (fun n : ℕ => (n : ℤ)) natural_decode).trans
    CurrentMFPortCast.port_natural_cast

#print axioms natural_decode
#print axioms decode_mf
end DiophantineConsistency.CurrentMFDecoderExplicit
