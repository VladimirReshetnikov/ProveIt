import DiophantineConsistency.Mixed121.Mixed121Masks
import DiophantineConsistency.Compact44.CompactMaskSlot
import DiophantineConsistency.ArithmeticWindowBits

/-! # The native-cell decoder of the 121x8801 low mask

This module ports, at width `121`, the three Compact44 modules that use their
width only as a literal: `CompactDummyBound`, `CompactMixedIncrement` and the
model part of `CompactListMask`. The accepted proof bodies are kept, and only
`67/66/65` become `121/120/119`. The helpers they call (`dig_mul_rep`,
`dig_add_one`, `noCarry_dig`, `dig_ofDigits`) are width-generic.

`recipe_digits` is the 121x8801 counterpart of
`CompactConcreteIncrement.recipe_digits`. Suppose `C − 1` has no carry against
`MC·rep(121·8801, N) + 1`. Then the native word `C` has `dig C 0 = 1`, and
every one of its `8801·N` cells is at most `3`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mixed121Increment
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticMaskConstants
open CompactListMask
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem forbidden_zero (x : V) (hx : x<Exp.exp 121)
    (h : NoCarry x (Exp.exp 121-1)) : x=0 := noCarry_ones 121 x hx h

theorem ordinary_le_one (x : V) (hx : x<Exp.exp 121)
    (h : NoCarry x (Exp.exp 121-2)) : x≤1 := by
  apply noCarry_ones_two 120
  · simpa only [show (120:V)+1=121 by norm_num] using hx
  · simpa only [show (120:V)+1=121 by norm_num] using h

/-- The special 121x8801 low-mask digit rho-4 permits a digit from 0 to 3.
The local digit bound and the no-carry mask relation are explicit inputs. -/
theorem dummy_le_three (x : V) (hx : x<Exp.exp 121)
    (h : NoCarry x (Exp.exp 121-4)) : x≤3 := by
  have hplus : Exp.exp (119:V)-1+1=Exp.exp 119 := tsub_add_cancel_of_le (one_le_exp _)
  have hE : Exp.exp (121:V)=4*(Exp.exp 119-1)+4 := calc
    _=2*(2*Exp.exp (119:V)) := by
      rw [show (121:V)=(119:V)+1+1 by norm_num,exp_succ,exp_succ]
    _=4*(Exp.exp 119-1)+4 := by
      conv_lhs => rw [←hplus]
      ring
  have hmask : Exp.exp (121:V)-4=2*(2*(Exp.exp 119-1))+0 := by
    rw [hE,add_tsub_cancel_right]
    ring
  have hr : x%2≤1 := lt_two_iff_le_one.mp (mod_lt _ (by norm_num))
  have h1in : NoCarry (2*(x/2)+x%2) (2*(2*(Exp.exp 119-1))+0) := by
    rw [div_add_mod x 2,←hmask]
    exact h
  have h1 := ((noCarry_binary (x/2) (2*(Exp.exp 119-1)) (x%2) 0 hr (by simp)).mp h1in).2
  have hr2 : (x/2)%2≤1 := lt_two_iff_le_one.mp (mod_lt _ (by norm_num))
  have h2in : NoCarry (2*((x/2)/2)+(x/2)%2) (2*(Exp.exp 119-1)+0) := by
    rw [div_add_mod (x/2) 2]
    simpa only [add_zero] using h1
  have h2 := ((noCarry_binary ((x/2)/2) (Exp.exp 119-1) ((x/2)%2) 0 hr2 (by simp)).mp h2in).2
  have he121 : Exp.exp (121:V)=2*Exp.exp 120 := by
    simpa only [show (120:V)+1=121 by norm_num] using (exp_succ (120:V))
  have he120 : Exp.exp (120:V)=2*Exp.exp 119 := by
    simpa only [show (119:V)+1=120 by norm_num] using (exp_succ (119:V))
  have hx120 : x/2<Exp.exp 120 := by
    apply div_lt_of_lt_mul
    rw [mul_comm,←he121]
    exact hx
  have hx119 : (x/2)/2<Exp.exp 119 := by
    apply div_lt_of_lt_mul
    rw [mul_comm,←he120]
    exact hx120
  have hz : (x/2)/2=0 := noCarry_ones 119 ((x/2)/2) hx119 h2
  have hq : x/2<2 := by
    have he := div_add_mod (x/2) 2
    rw [hz] at he
    rw [←he]
    simp
  have hq1 : x/2≤1 := lt_two_iff_le_one.mp hq
  calc
    x=2*(x/2)+x%2 := (div_add_mod x 2).symm
    _≤2*1+1 := add_le_add (mul_le_mul_of_nonneg_left hq1 (by simp)) hr
    _=3 := by ring

theorem decode_mixed_increment (m N C MC : V) (hm : 0 < m) (hN : 0 < N)
    (hMC : MC < Exp.exp (121*m))
    (hclass : ∀ j < m, dig 121 MC j = Exp.exp 121-1 ∨
      dig 121 MC j = Exp.exp 121-2 ∨ dig 121 MC j = Exp.exp 121-4)
    (hMC0 : dig 121 MC 0 = Exp.exp 121-2) (hC : 1 ≤ C)
    (hnc : NoCarry (C-1) (MC * rep (121*m) N + 1)) :
    dig 121 C 0 = 1 ∧ ∀ k < m*N, dig 121 C k ≤ 3 := by
  have h2 : (2:V) ≤ Exp.exp 121 := by
    simpa using exp_monotone_le.mpr (show (1:V) ≤ 121 by norm_num)
  set e := Exp.exp (121:V)-2
  have he : Exp.exp (121:V) = e+2 := (tsub_add_cancel_of_le h2).symm
  have hρ1 : Exp.exp (121:V)-1=e+1 := by
    rw [he, show e+2=(e+1)+1 by ring, add_tsub_cancel_right]
  have hmN : 0 < m*N := mul_pos hm hN
  have hJ : ∀ k < m*N, dig 121 (MC * rep (121*m) N) k = dig 121 MC (k % m) :=
    dig_mul_rep 121 m MC hMC N
  have h0 : dig 121 (MC * rep (121*m) N) 0 = e := by
    rw [hJ 0 hmN, zero_mod, hMC0]
  obtain ⟨hinc0, hinck⟩ := dig_add_one 121 (MC * rep (121*m) N)
    (by rw [h0, he]; exact (add_lt_add_iff_left e).mpr one_lt_two)
  have hz : dig 121 (C-1) 0 = 0 := by
    apply noCarry_ones 121 _ (dig_lt 121 _ 0)
    simpa only [hinc0, h0, ←hρ1] using noCarry_dig 121 _ _ 0 hnc
  have hC1 : C-1+1=C := tsub_add_cancel_of_le hC
  obtain ⟨hc0, hck⟩ := dig_add_one 121 (C-1)
    (by rw [hz, zero_add, he]; exact lt_of_lt_of_le one_lt_two (le_add_of_nonneg_left (by simp)))
  rw [hC1] at hc0 hck
  have digit_pos : ∀ k < m*N, 0 < k → NoCarry (dig 121 C k) (dig 121 MC (k % m)) := by
    intro k hk hk0
    simpa only [hinck k hk0, hJ k hk, ←hck k hk0] using noCarry_dig 121 _ _ k hnc
  refine ⟨by rw [hc0,hz,zero_add], ?_⟩
  intro k hk
  rcases zero_or_succ k with rfl | ⟨j,rfl⟩
  · rw [hc0,hz,zero_add]; norm_num
  · have hc := digit_pos (j+1) hk (by simp)
    rcases hclass ((j+1)%m) (mod_lt _ hm) with h1 | h2 | h4
    · rw [h1] at hc
      rw [forbidden_zero _ (dig_lt 121 C _) hc]; norm_num
    · rw [h2] at hc
      exact le_trans (ordinary_le_one _ (dig_lt 121 C _) hc) (by norm_num)
    · rw [h4] at hc
      exact dummy_le_three _ (dig_lt 121 C _) hc

theorem model_mask_class (len special : ℕ) (S : Finset ℕ) (j : V) (hj : j < (len:V)) :
    let M : V := (Nat.ofDigits (2^121) (digits (2^121) len special S) : ℕ)
    dig 121 M j = Exp.exp 121-1 ∨ dig 121 M j = Exp.exp 121-2 ∨
      dig 121 M j = Exp.exp 121-4 := by
  obtain ⟨j₀,rfl⟩ := eq_nat_of_lt_nat (n := len) hj
  have hj₀ : j₀ < len := by exact_mod_cast hj
  have hd := dig_ofDigits (V:=V) 121 (digits (2^121) len special S)
    (digits_lt _ _ _ _ (by norm_num)) j₀
  rw [digits_getD _ _ _ _ hj₀] at hd
  have hsub (r : ℕ) (hr : r ≤ 2^121) :
      ((2^121-r : ℕ):V) = Exp.exp (121:V)-(r:V) := by
    have h1 : 2^121-r+r=2^121 := Nat.sub_add_cancel hr
    have h2 : ((2^121-r : ℕ):V)+(r:V)=((2^121:ℕ):V) := by exact_mod_cast h1
    have h3 : ((2^121:ℕ):V)=Exp.exp (121:V) := by simpa using (cast_exp (V:=V) 121).symm
    rw [h3] at h2
    exact eq_tsub_of_add_eq h2
  unfold digit at hd
  split_ifs at hd
  · rw [hsub 4 (by norm_num)] at hd
    exact Or.inr (Or.inr (by simpa using hd))
  · rw [hsub 2 (by norm_num)] at hd
    exact Or.inr (Or.inl (by simpa using hd))
  · rw [hsub 1 (by norm_num)] at hd
    exact Or.inl (by simpa using hd)
theorem model_mask_lt (len special : ℕ) (S : Finset ℕ) :
    ((Nat.ofDigits (2^121) (digits (2^121) len special S) : ℕ):V) <
      Exp.exp ((121:V)*(len:V)) := by
  have h := ofDigits_lt_exp (V:=V) 121 (digits (2^121) len special S)
    (digits_lt _ _ _ _ (by norm_num))
  simpa only [digits_length, Nat.cast_ofNat] using h

theorem model_mask_origin (len special : ℕ) (S : Finset ℕ)
    (hlen : 0 < len) (hspecial : special ≠ 0) (hS : 0 ∈ S) :
    dig 121 ((Nat.ofDigits (2^121) (digits (2^121) len special S) : ℕ):V) 0 =
      Exp.exp 121-2 := by
  have hd := dig_ofDigits (V:=V) 121 (digits (2^121) len special S)
    (digits_lt _ _ _ _ (by norm_num)) 0
  rw [digits_getD _ _ _ _ hlen] at hd
  have h1 : (2:ℕ) ≤ 2^121 := by norm_num
  have h2 : ((2^121-2 : ℕ):V)+(2:V)=((2^121:ℕ):V) := by
    exact_mod_cast (Nat.sub_add_cancel h1)
  have h3 : ((2^121:ℕ):V)=Exp.exp (121:V) := by simpa using (cast_exp (V:=V) 121).symm
  rw [h3] at h2
  have hsub : ((2^121-2 : ℕ):V)=Exp.exp (121:V)-2 := eq_tsub_of_add_eq h2
  simp only [digit, if_neg (Ne.symm hspecial), if_pos hS] at hd
  rw [hsub] at hd
  simpa only [Nat.cast_zero, Nat.cast_ofNat] using hd

/-! ## The 121x8801 low mask -/

theorem low_class (j : V) (hj : j < 8801) :
    dig 121 ((Mixed121Ports.lowNat : ℕ) : V) j = Exp.exp 121-1 ∨
      dig 121 ((Mixed121Ports.lowNat : ℕ) : V) j = Exp.exp 121-2 ∨
      dig 121 ((Mixed121Ports.lowNat : ℕ) : V) j = Exp.exp 121-4 := by
  have h := Mixed121Increment.model_mask_class 8801 1063 Mixed121Ports.maskSupport j (by simpa using hj)
  simpa only [Mixed121Ports.lowNat, Mixed121Ports.radix] using h

theorem low_origin : dig 121 ((Mixed121Ports.lowNat : ℕ) : V) 0 = Exp.exp 121-2 := by
  have h := Mixed121Increment.model_mask_origin (V:=V) 8801 1063 Mixed121Ports.maskSupport (by norm_num)
    (by norm_num) Mixed121Ports.zero_mem_support
  simpa only [Mixed121Ports.lowNat, Mixed121Ports.radix] using h

/-- The native cells of `C` from the low-mask no-carry condition. -/
theorem recipe_digits (N C : V) (hN : 0 < N) (hC : 1 ≤ C)
    (hnc : NoCarry (C-1) (((Mixed121Ports.lowNat : ℕ) : V) * rep (121*8801) N + 1)) :
    dig 121 C 0 = 1 ∧ ∀ k < 8801*N, dig 121 C k ≤ 3 :=
  Mixed121Increment.decode_mixed_increment 8801 N C ((Mixed121Ports.lowNat : ℕ) : V) (by norm_num) hN
    Mixed121Masks.model_low_lt (fun j hj => low_class j hj) low_origin hC hnc
end Mixed121Increment
#print axioms Mixed121Increment.forbidden_zero
#print axioms Mixed121Increment.ordinary_le_one
#print axioms Mixed121Increment.dummy_le_three
#print axioms Mixed121Increment.decode_mixed_increment
#print axioms Mixed121Increment.model_mask_class
#print axioms Mixed121Increment.model_mask_origin
#print axioms Mixed121Increment.recipe_digits
