import DiophantineConsistency.Mixed121.Mixed121Increment
import DiophantineConsistency.ArithmeticPackingBlocks

/-! # Single-bit pulse safety and the low-mask residue, at 121x8801

The 121x8801 counterparts of Compact44's `CompactPulseBitSafety` and
`CompactLowModFour`.

* `pulse_preserves_noCarry` (generic): adding `2^k` to a word that is
  carry-free against a mask keeps it so, if both have bit `k` clear.
* `low_mask_bit`: `MC` has bit `121·1063` clear. Its digit at the dummy cell
  `1063` is `B − 4`.
* `low_pulse_noCarry`: the specialization to `MC` at that bit.
* `low_mod_four`: `MC ≡ 2 (mod 4)`. Its digit `0` is `B − 2`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Mixed121PulseBit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticBinaryPopulation ArithmeticWindowDigits ArithmeticPackingBlocks
  ArithmeticMaskConstants
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem pulse_preserves_noCarry (x m k : V) (h : NoCarry x m)
    (hx : fbit x k = 0) (hm : fbit m k = 0) :
    NoCarry (x + Exp.exp k) m := by
  let a := x / Exp.exp k
  let b := m / Exp.exp k
  let A := x % Exp.exp k
  let B := m % Exp.exp k
  have hA : A < Exp.exp k := mod_lt _ (exp_pos k)
  have hB : B < Exp.exp k := mod_lt _ (exp_pos k)
  have hlow : NoCarry A B := by
    simpa [A, B, dig_zero_index] using noCarry_dig k x m 0 h
  have hhigh : NoCarry a b := by
    rw [noCarry_iff] at h ⊢
    intro i
    simpa [a, b, fbit_div_exp] using h (k+i)
  have ha0 : a % 2 = 0 := by simpa [a, fbit_eq_div] using hx
  have hb0 : b % 2 = 0 := by simpa [b, fbit_eq_div] using hm
  have ha : 2*(a/2)+0 = a := by simpa [ha0] using div_add_mod a 2
  have hb : 2*(b/2)+0 = b := by simpa [hb0] using div_add_mod b 2
  have htail : NoCarry (a/2) (b/2) := by
    have he := (noCarry_binary (a/2) (b/2) 0 0 (by simp) (by simp)).mp (by simpa [ha, hb] using hhigh)
    exact he.2
  have hhigh' : NoCarry (a+1) b := by
    have he := (noCarry_binary (a/2) (b/2) 1 0 (by simp) (by simp)).mpr ⟨by simp, htail⟩
    have haa : 2*(a/2)+1 = a+1 := by rw [← ha]; simp
    rw [haa, hb] at he
    exact he
  have hnc := noCarry_concat hA hB hlow hhigh'
  have hx' : a * Exp.exp k + A = x := by simpa [a, A, mul_comm] using div_add_mod x (Exp.exp k)
  have hm' : b * Exp.exp k + B = m := by simpa [b, B, mul_comm] using div_add_mod m (Exp.exp k)
  have hx'' : (a+1)*Exp.exp k+A = x+Exp.exp k := by rw [← hx']; ring
  rw [← hx'', ← hm']
  exact hnc

/-- The special low-mask phase 1063 has its least significant bit clear. -/
theorem low_mask_bit :
    fbit ((Mixed121Ports.lowNat : ℕ) : V) (121*1063) = 0 := by
  have hd := dig_ofDigits (V:=V) 121
    (CompactListMask.digits (2^121) 8801 1063 Mixed121Ports.maskSupport)
    (CompactListMask.digits_lt _ _ _ _ (by norm_num)) 1063
  rw [CompactListMask.digits_getD _ _ _ _ (by norm_num)] at hd
  simp only [CompactListMask.digit, ↓reduceIte] at hd
  have hf := fbit_dig (121:V) ((Mixed121Ports.lowNat : ℕ) : V) 1063 0 (by norm_num)
  have hd' : dig 121 ((Mixed121Ports.lowNat : ℕ) : V) 1063 = ((2^121-4 : ℕ) : V) := by
    rw [Mixed121Masks.lowNat_eq]; exact hd
  rw [hd'] at hf
  have hz : fbit (((2^121-4 : ℕ) : V)) 0 = 0 := by
    rw [fbit_eq_div, exp_zero, Arithmetic.div_one]
    change (((2^121-4 : ℕ) : V) % ((2:ℕ):V)) = 0
    rw [← cast_mod]
    norm_num
  simpa only [mul_zero, add_zero] using hf.symm.trans hz

/-- The pulse at the dummy bit of `MC`; an empty baseline bit is required. -/
theorem low_pulse_noCarry (x : V) (h : NoCarry x ((Mixed121Ports.lowNat : ℕ) : V))
    (hx : fbit x (121*1063) = 0) :
    NoCarry (x + Exp.exp (121*1063)) ((Mixed121Ports.lowNat : ℕ) : V) :=
  pulse_preserves_noCarry x _ (121*1063) h hx low_mask_bit

/-- `MC` has residue two modulo four in every model. -/
theorem low_mod_four : ((Mixed121Ports.lowNat : ℕ) : V) % 4 = 2 := by
  let M : V := ((Mixed121Ports.lowNat : ℕ) : V)
  have ho : M % Exp.exp (121:V) = Exp.exp (121:V)-2 := by
    simpa only [M, dig_zero_index] using (Mixed121Increment.low_origin (V:=V))
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

#print axioms Mixed121PulseBit.pulse_preserves_noCarry
#print axioms Mixed121PulseBit.low_mask_bit
#print axioms Mixed121PulseBit.low_pulse_noCarry
#print axioms Mixed121PulseBit.low_mod_four
end Mixed121PulseBit
