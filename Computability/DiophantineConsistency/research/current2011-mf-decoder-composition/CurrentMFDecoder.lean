import CurrentMFNaturalSum
import CurrentMFPortCast

/-! Exact once-shifted high-mask byte decoder, composed from checked lemmas. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.CurrentMFDecoder
open CurrentMFRecipe
attribute [local irreducible] rho maskDigits CurrentMasks2011.radix
  CurrentMasks2011.highPort CurrentMasks2011.beta CurrentWindowCarry2011.ports

def shiftedValue : ℕ := Nat.ofDigits rho maskDigits + (rho ^ 2011 - 1)
def bigBytes : List ℕ := (Nat.digits 256 shiftedValue).reverse

theorem natural_decode :
    (Nat.ofDigits 256 bigBytes.reverse : ℕ) =
      CurrentMasks2011.highPort + CurrentMasks2011.beta := by
  rw [bigBytes, List.reverse_reverse, Nat.ofDigits_digits]
  exact CurrentMFNaturalSum.natural_sum

theorem decode_mf :
    ((Nat.ofDigits 256 bigBytes.reverse : ℕ) : ℤ) = CurrentWindowCarry2011.ports 3 :=
  (congrArg (fun n : ℕ => (n : ℤ)) natural_decode).trans
    CurrentMFPortCast.port_natural_cast

#print axioms natural_decode
#print axioms decode_mf
end DiophantineConsistency.CurrentMFDecoder
