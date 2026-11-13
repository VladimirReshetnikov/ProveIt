import DiophantineConsistency.Source34.Source34Increment
import DiophantineConsistency.Mixed121.Mixed121PulseBit

/-! # Single-bit pulse safety and the low-mask residue, at the source34 ports

`Mixed121PulseBit` at the source34 tuple. The pulse lemma
`Mixed121PulseBit.pulse_preserves_noCarry` is generic and used directly. The
three statements about the concrete low mask are re-declared at
`Source34Ports.lowNat`, whose digits have the same shape (`B − 4` at the
dummy cell `1063`, `B − 2` at cell `0`):

* `low_mask_bit`: `MC` has bit `121·1063` clear;
* `low_pulse_noCarry`: the pulse at that bit;
* `low_mod_four`: `MC ≡ 2 (mod 4)`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Source34PulseBit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticBinaryPopulation ArithmeticWindowDigits ArithmeticPackingBlocks
  ArithmeticMaskConstants
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The special low-mask phase 1063 has its least significant bit clear. -/
theorem low_mask_bit :
    fbit ((Source34Ports.lowNat : ℕ) : V) (121*1063) = 0 := by
  have hd := dig_ofDigits (V:=V) 121
    (CompactListMask.digits (2^121) 8801 1063 Source34Ports.maskSupport)
    (CompactListMask.digits_lt _ _ _ _ (by norm_num)) 1063
  rw [CompactListMask.digits_getD _ _ _ _ (by norm_num)] at hd
  simp only [CompactListMask.digit, ↓reduceIte] at hd
  have hf := fbit_dig (121:V) ((Source34Ports.lowNat : ℕ) : V) 1063 0 (by norm_num)
  have hd' : dig 121 ((Source34Ports.lowNat : ℕ) : V) 1063 = ((2^121-4 : ℕ) : V) := by
    rw [Source34Masks.lowNat_eq]; exact hd
  rw [hd'] at hf
  have hz : fbit (((2^121-4 : ℕ) : V)) 0 = 0 := by
    rw [fbit_eq_div, exp_zero, Arithmetic.div_one]
    change (((2^121-4 : ℕ) : V) % ((2:ℕ):V)) = 0
    rw [← cast_mod]
    norm_num
  simpa only [mul_zero, add_zero] using hf.symm.trans hz

/-- The pulse at the dummy bit of `MC`; an empty baseline bit is required. -/
theorem low_pulse_noCarry (x : V) (h : NoCarry x ((Source34Ports.lowNat : ℕ) : V))
    (hx : fbit x (121*1063) = 0) :
    NoCarry (x + Exp.exp (121*1063)) ((Source34Ports.lowNat : ℕ) : V) :=
  Mixed121PulseBit.pulse_preserves_noCarry x _ (121*1063) h hx low_mask_bit

/-- `MC` has residue two modulo four in every model. -/
theorem low_mod_four : ((Source34Ports.lowNat : ℕ) : V) % 4 = 2 := by
  let M : V := ((Source34Ports.lowNat : ℕ) : V)
  have ho : M % Exp.exp (121:V) = Exp.exp (121:V)-2 := by
    simpa only [M, dig_zero_index] using (Source34Increment.low_origin (V:=V))
  have hp : Exp.exp (119:V)-1+1=Exp.exp 119 := tsub_add_cancel_of_le (one_le_exp _)
  have hE : Exp.exp (121:V)=4*(Exp.exp 119-1)+4 := calc
    _=2*(2*Exp.exp (119:V)) := by
      rw [show (121:V)=(119:V)+1+1 by norm_num,exp_succ,exp_succ]
    _=4*(Exp.exp 119-1)+4 := by
      conv_lhs => rw [←hp]
      ring
  have hr : (Exp.exp (121:V)-2)%4=2 := by
    rw [hE, show (4:V)*(Exp.exp 119-1)+4 = (4*(Exp.exp 119-1)+2)+2 by ring,
      add_tsub_cancel_right,
      add_comm, mod_add_mul' _ _ (by norm_num), mod_eq_self_of_lt (by norm_num : (2:V)<4)]
  have he2 : Exp.exp (2:V) = 4 := by
    rw [show (2:V)=1+1 by norm_num,exp_succ,exp_one]
    norm_num
  have hm := mod_mod_of_le (1:V) M 2 121 (by norm_num)
  simp only [one_mul, he2] at hm
  rw [ho, hr] at hm
  exact hm.symm

#print axioms Source34PulseBit.low_mask_bit
#print axioms Source34PulseBit.low_pulse_noCarry
#print axioms Source34PulseBit.low_mod_four
end Source34PulseBit
