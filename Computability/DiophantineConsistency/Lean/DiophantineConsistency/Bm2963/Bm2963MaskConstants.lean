import DiophantineConsistency.ArithmeticMaskConstants
import DiophantineConsistency.Bm2963.Bm2963Kernel

/-! # The block-mask2963 standard constants inside every model of IΣ1

The counterpart of `ArithmeticMaskConstants`. Facts about the 139261-bit
numerals `lowPort`, `highPort` and the kernel `K` are transferred from ℕ
through `Nat.cast`, never by evaluating the numerals in the model: digits come
from the standard digit lists of `Bm2963MaskData`, populations from their
digit populations, and the kernel from its finite term sum. The generic cast,
digit and population lemmas are the 2011 ones (`ArithmeticMaskConstants`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Bm2963MaskConstants
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinaryPopulation ArithmeticWindowDigits
open ArithmeticMaskConstants (cast_exp cast_mod dig_ofDigits population_ofDigits ofDigits_lt_exp)
open Bm2963MaskData (lowDigits lowDigits_lt lowDigits_length lowDigits_getD lowPort_ofDigits
  radix_eq highDigits highDigits_lt' highDigits_length highDigits_zero highPort_ofDigits
  digit_population)
attribute [local irreducible] Bm2963Kernel.K Bm2963MaskData.beta
  Bm2963MaskData.lowPort Bm2963MaskData.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The masks -/

theorem lowPort_lt_exp : (Bm2963MaskData.lowPort : V) < Exp.exp ((47:V)*2963) := by
  have h := ofDigits_lt_exp (V:=V) 47 lowDigits (fun x hx => lowDigits_lt hx)
  rw [lowDigits_length, ← radix_eq, ← lowPort_ofDigits] at h
  simpa using h

theorem highPort_lt_exp : (Bm2963MaskData.highPort : V) < Exp.exp ((47:V)*2963) := by
  have h := ofDigits_lt_exp (V:=V) 47 highDigits (fun x hx => highDigits_lt' hx)
  rw [highDigits_length, ← highPort_ofDigits] at h
  simpa using h

/-- The low support `Es = [0,951) ∪ [960,986) ∪ {1005}` as an internal Σ0 predicate. -/
def inS (j : V) : Prop := j < 951 ∨ (960 ≤ j ∧ j < 986) ∨ j = 1005

theorem inS_cast (j : ℕ) : inS (j:V) ↔ (j < 951 ∨ (960 ≤ j ∧ j < 986) ∨ j = 1005) := by
  unfold inS
  norm_cast

theorem inS_zero : inS (0:V) := Or.inl (by simp)

private theorem low_digit (j : V) (hj : j < 2963) :
    ∃ j₀ : ℕ, j = j₀ ∧ j₀ < 2963 ∧ dig (47:V) (Bm2963MaskData.lowPort:V) j =
      ((lowDigits.getD j₀ 0 : ℕ) : V) := by
  obtain ⟨j₀, rfl⟩ := eq_nat_of_lt_nat (n := 2963) (by simpa using hj)
  have hj₀ : j₀ < 2963 := by exact_mod_cast hj
  refine ⟨j₀, rfl, hj₀, ?_⟩
  have h := dig_ofDigits (V:=V) 47 lowDigits (fun x hx => lowDigits_lt hx) j₀
  rw [← radix_eq, ← lowPort_ofDigits] at h
  simpa using h

private theorem cast_radix_sub (b : ℕ) (hb : b ≤ 2^47) :
    ((Bm2963MaskData.radix - b : ℕ) : V) = Exp.exp (47:V) - (b:V) := by
  have h1 : Bm2963MaskData.radix - b + b = Bm2963MaskData.radix :=
    Nat.sub_add_cancel (by rw [radix_eq]; exact hb)
  have h2 : ((Bm2963MaskData.radix - b : ℕ) : V) + (b:V) = (Bm2963MaskData.radix : V) := by
    exact_mod_cast h1
  have h3 : ((Bm2963MaskData.radix : ℕ) : V) = Exp.exp (47:V) := by
    have := cast_exp (V:=V) 47
    rw [Nat.cast_ofNat] at this
    rw [this, radix_eq]
  rw [h3] at h2
  exact eq_tsub_of_add_eq h2

theorem lowPort_digit_in (j : V) (hj : j < 2963) (hS : inS j) :
    dig (47:V) (Bm2963MaskData.lowPort:V) j = Exp.exp 47 - 2 := by
  obtain ⟨j₀, rfl, hj₀, h⟩ := low_digit j hj
  rw [h, lowDigits_getD j₀ hj₀, if_pos ((inS_cast j₀).mp hS), cast_radix_sub 2 (by decide)]
  simp

theorem lowPort_digit_out (j : V) (hj : j < 2963) (hS : ¬ inS j) :
    dig (47:V) (Bm2963MaskData.lowPort:V) j = Exp.exp 47 - 1 := by
  obtain ⟨j₀, rfl, hj₀, h⟩ := low_digit j hj
  rw [h, lowDigits_getD j₀ hj₀, if_neg (fun h' => hS ((inS_cast j₀).mpr h')),
    cast_radix_sub 1 (by decide)]
  simp

/-- The high-mask digits are the standard list `highDigits`. -/
theorem highPort_digit (j : ℕ) :
    dig (47:V) (Bm2963MaskData.highPort:V) (j:V) =
      ((highDigits.getD j 0 : ℕ) : V) := by
  have h := dig_ofDigits (V:=V) 47 highDigits (fun x hx => highDigits_lt' hx) j
  rw [← highPort_ofDigits] at h
  simpa using h

theorem highPort_digit_zero : dig (47:V) (Bm2963MaskData.highPort:V) 0 = 4 := by
  have h := highPort_digit (V:=V) 0
  rw [highDigits_zero] at h
  simpa using h

theorem ports_population :
    population (Bm2963MaskData.lowPort:V) + population (Bm2963MaskData.highPort:V) =
      139261 := by
  have h1 := population_ofDigits (V:=V) 47 lowDigits (fun x hx => lowDigits_lt hx)
  have h2 := population_ofDigits (V:=V) 47 highDigits (fun x hx => highDigits_lt' hx)
  rw [← radix_eq, ← lowPort_ofDigits] at h1
  rw [← highPort_ofDigits] at h2
  rw [h1, h2, ← Nat.cast_add, digit_population]
  simp

theorem lowPort_even : (Bm2963MaskData.lowPort:V) % 2 = 0 := by
  have h0 := lowPort_digit_in (V:=V) 0 (by norm_num) inS_zero
  rw [dig_zero_index] at h0
  have hρ : Exp.exp (47:V) = 2 * Exp.exp 46 := by
    rw [show (47:V) = 46 + 1 by norm_num, exp_succ]
  obtain ⟨e, he⟩ : ∃ e, Exp.exp (46:V) = e + 1 :=
    ⟨Exp.exp 46 - 1, (tsub_add_cancel_of_le (one_le_exp _)).symm⟩
  have hX := div_add_mod (Bm2963MaskData.lowPort:V) (Exp.exp 47)
  rw [h0, hρ, he, show 2*(e+1) - 2 = 2*e by
    rw [show (2:V)*(e+1) = 2*e+2 by ring, add_tsub_cancel_right]] at hX
  rw [← hX, show ∀ Y : V, 2*(e+1)*Y + 2*e = 2*((e+1)*Y + e) from fun Y => by ring]
  exact mod_mul_self_right _ _

theorem highPort_mod_eight : (Bm2963MaskData.highPort:V) % 8 = 4 := by
  have h0 := highPort_digit_zero (V:=V)
  rw [dig_zero_index] at h0
  have h8 : Exp.exp (3:V) = 8 := by
    have := cast_exp (V:=V) 3
    rw [Nat.cast_ofNat] at this
    rw [this]; norm_num
  have hρ : Exp.exp (47:V) = 8 * Exp.exp 44 := by
    rw [show (47:V) = 3 + 44 by norm_num, exp_add, h8]
  have hX := div_add_mod (Bm2963MaskData.highPort:V) (Exp.exp 47)
  rw [h0, hρ] at hX
  rw [← hX, show ∀ Y : V, 8 * Exp.exp 44 * Y + 4 = (Exp.exp 44 * Y) * 8 + 4 from
    fun Y => by ring]
  exact mod_mul_add_of_lt _ _ (by norm_num)

theorem highPort_pos : (0:V) < (Bm2963MaskData.highPort:V) := by
  apply pos_iff_ne_zero.mpr
  intro h
  have h0 := highPort_digit_zero (V:=V)
  rw [h] at h0
  simp [dig] at h0

/-! ### The kernel -/

theorem cast_radix_pow (e : ℕ) :
    ((Bm2963MaskData.radix : ℕ) : V)^e = Exp.exp (47 * (e:V)) := by
  have h : (47:V) * (e:V) = ((47*e : ℕ) : V) := by norm_cast
  rw [h, cast_exp, radix_eq, pow_mul]
  push_cast
  rfl

theorem kernel_sum : (Bm2963Kernel.K : V) =
    ∑ t : Bm2963Kernel.Term,
      (Bm2963Kernel.coefficient t : V) * Exp.exp (47 * (Bm2963Kernel.exponent t : V)) := by
  have hK : Bm2963Kernel.K = ∑ t : Bm2963Kernel.Term,
      Bm2963Kernel.coefficient t * Bm2963MaskData.radix ^ Bm2963Kernel.exponent t := by
    unfold Bm2963Kernel.K Bm2963Kernel.rawWord; rfl
  rw [hK, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Nat.cast_mul, Nat.cast_pow, cast_radix_pow]

theorem kernel_mass :
    ∑ t : Bm2963Kernel.Term, (Bm2963Kernel.coefficient t : V) = 3829914518400945 := by
  rw [← Nat.cast_sum, Bm2963Kernel.coefficient_mass]
  simp

end Bm2963MaskConstants

#print axioms Bm2963MaskConstants.lowPort_lt_exp
#print axioms Bm2963MaskConstants.highPort_lt_exp
#print axioms Bm2963MaskConstants.lowPort_digit_in
#print axioms Bm2963MaskConstants.lowPort_digit_out
#print axioms Bm2963MaskConstants.highPort_digit
#print axioms Bm2963MaskConstants.highPort_digit_zero
#print axioms Bm2963MaskConstants.ports_population
#print axioms Bm2963MaskConstants.lowPort_even
#print axioms Bm2963MaskConstants.highPort_mod_eight
#print axioms Bm2963MaskConstants.highPort_pos
#print axioms Bm2963MaskConstants.kernel_sum
#print axioms Bm2963MaskConstants.kernel_mass
