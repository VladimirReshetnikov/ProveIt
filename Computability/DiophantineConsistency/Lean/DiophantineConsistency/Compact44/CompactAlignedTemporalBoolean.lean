import DiophantineConsistency.Compact44.CompactWordProperties
import DiophantineConsistency.Compact44.CompactBitRotation
import DiophantineConsistency.Compact44.TemporalOtherWindows
import DiophantineConsistency.ArithmeticModularCancellation

/-! Aligned temporal rotation preserves Boolean radix digits. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactAlignedTemporalBoolean
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits
open DiophantineConsistency.ArithmeticCyclicWord
open CompactBitRotation CompactConstructedWord CompactWordProperties
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem aligned_digit (C n e k : V) (hn : 0 < n) (hk : k < n)
    (hC : C < Exp.exp (67*n)) :
    dig 67 (temporalWord n (67*e) C) k = dig 67 C (cyc n k (e%n)) := by
  have he : (67*e)%(67*n) = 67*(e%n) :=
    DiophantineConsistency.ArithmeticModularCancellation.mul_mod_mul (by norm_num) hn
  exact TemporalOtherWindows.aligned C n (67*e) k (e%n) hk (mod_lt _ hn) he hC

theorem word_temporal_boolean (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N e k : V) (hN : 0 < N) (hk : k < 8807*N) :
    dig 67 (temporalWord (8807*N) (67*e) (packedWord row dummy N)) k ≤ 1 := by
  have hn : 0 < (8807:V)*N := mul_pos (by norm_num) hN
  have hC : packedWord row dummy N < Exp.exp (67*(8807*N)) := by
    simpa only [mul_assoc] using packedWord_lt row dummy N
  rw [aligned_digit _ _ _ _ hn hk hC]
  exact word_cap row dummy N _ (cyc_lt hn _ _)

#print axioms CompactAlignedTemporalBoolean.aligned_digit
#print axioms CompactAlignedTemporalBoolean.word_temporal_boolean
end CompactAlignedTemporalBoolean
