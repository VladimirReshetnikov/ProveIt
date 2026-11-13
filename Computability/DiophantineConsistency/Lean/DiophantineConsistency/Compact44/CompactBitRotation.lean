import DiophantineConsistency.ArithmeticCyclicWord
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactBitRotation
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticCyclicWord ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The unrestricted exponent gives a bit rotation, without radix alignment. -/
noncomputable def temporalWord (n e C : V) : V := rot 1 (67*n) C (e % (67*n))

theorem temporal_mod (n e C : V) (hn : 0<n)
    (hM : 0<Exp.exp (67*n)-1) :
    (Exp.exp e*C) % (Exp.exp (67*n)-1) =
      temporalWord n e C % (Exp.exp (67*n)-1) := by
  have hlen : 0<67*n := mul_pos (by norm_num) hn
  have h := exp_mul_mod_rot (1:V) (67*n) e C hlen (by simpa only [one_mul] using hM)
  simpa only [temporalWord,one_mul] using h

theorem temporal_word_lt (n e C : V) (hn : 0<n)
    (hC : C<Exp.exp (67*n)) : temporalWord n e C<Exp.exp (67*n) := by
  have hlen : 0<67*n := mul_pos (by norm_num) hn
  have h := rot_lt (1:V) (67*n) C (e%(67*n)) (le_of_lt (mod_lt e hlen))
    (by simpa only [one_mul] using hC)
  simpa only [temporalWord,one_mul] using h

theorem temporal_digit_lt (n e C k : V) :
    dig 67 (temporalWord n e C) k < Exp.exp 67 := dig_lt 67 _ k

theorem temporal_digit_le (n e C k : V) :
    dig 67 (temporalWord n e C) k ≤ Exp.exp 67-1 := by
  apply le_tsub_of_add_le_left
  simpa only [add_comm] using lt_iff_succ_le.mp (temporal_digit_lt n e C k)

/-- Replace only the exponential term; all other contributions remain explicit. -/
theorem replace_temporal (n e C A F : V) (hn : 0<n)
    (hM : 0<Exp.exp (67*n)-1)
    (h : (A+Exp.exp e*C)%(Exp.exp (67*n)-1)=F) :
    (A+temporalWord n e C)%(Exp.exp (67*n)-1)=F := by
  have ht := temporal_mod n e C hn hM
  have heq : (A+Exp.exp e*C)%(Exp.exp (67*n)-1) =
      (A+temporalWord n e C)%(Exp.exp (67*n)-1) := by
    rw [mod_add hM,ht,←mod_add hM]
  exact heq.symm.trans h
end CompactBitRotation
#print axioms CompactBitRotation.temporal_mod
#print axioms CompactBitRotation.temporal_word_lt
#print axioms CompactBitRotation.temporal_digit_lt
#print axioms CompactBitRotation.temporal_digit_le
#print axioms CompactBitRotation.replace_temporal
