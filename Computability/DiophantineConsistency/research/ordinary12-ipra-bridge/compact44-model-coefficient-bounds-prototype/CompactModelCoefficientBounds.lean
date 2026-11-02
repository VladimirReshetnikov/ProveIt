import DiophantineConsistency.CompactCoefficientDecoder
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactModelCoefficientBounds
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem exp_nat_cast (n : ℕ) : Exp.exp (n:V)=(2:V)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add,Nat.cast_one,exp_succ,ih,pow_succ,mul_comm]

theorem selector_bounds (i : Fin 943) :
    0 < ((CompactCoefficientMass.selector (Compact943Data.row i):ℕ):V) ∧
      ((CompactCoefficientMass.selector (Compact943Data.row i):ℕ):V) < Exp.exp 51 := by
  rw [CompactCoefficientDecoder.selector_model]
  have hv := Compact943Decoder.tileValue_bounds (V:=V) i
  have hr : 0 < Exp.exp (41:V) := lt_trans hv.1 hv.2
  have hsub : Exp.exp 41 - Compact943Decoder.tileValue (V:=V) i < Exp.exp 41 :=
    tsub_lt_self hr hv.1
  have hsub' : Exp.exp 41 - Compact943Decoder.tileValue (V:=V) i + 1 ≤ Exp.exp 41 :=
    lt_iff_succ_le.mp hsub
  have h10 : Exp.exp (10:V)=(2:V)^10 := by
    simpa only [Nat.cast_ofNat] using exp_nat_cast (V:=V) 10
  have h10big : 1 < Exp.exp (10:V) := by rw [h10]; norm_num
  constructor
  · exact add_pos_of_pos_of_nonneg (by simp) (by simp)
  · calc
      1 + Exp.exp 10 * (Exp.exp 41 - Compact943Decoder.tileValue (V:=V) i)
          < Exp.exp 10 * (Exp.exp 41 - Compact943Decoder.tileValue (V:=V) i) + Exp.exp 10 := by
            simpa only [add_comm] using add_lt_add_right h10big
              (Exp.exp 10 * (Exp.exp 41 - Compact943Decoder.tileValue (V:=V) i))
      _ = Exp.exp 10 * ((Exp.exp 41 - Compact943Decoder.tileValue (V:=V) i)+1) := by ring
      _ ≤ Exp.exp 10 * Exp.exp 41 := mul_le_mul_of_nonneg_left hsub' (by simp)
      _ = Exp.exp 51 := by rw [←exp_add,show (10:V)+41=51 by norm_num]

theorem copy_coefficient_bound (j : Fin 41) :
    ((2^(10+j.val):ℕ):V) < Exp.exp 51 := by
  have hnat : ∀ j : Fin 41, 2^(10+j.val) < 2^51 := by decide
  have hm : ((2^(10+j.val):ℕ):V) < ((2^51:ℕ):V) := by exact_mod_cast hnat j
  have he : Exp.exp (51:V) = ((2^51:ℕ):V) := by
    have he' := exp_nat_cast (V:=V) 51
    simpa only [Nat.cast_ofNat,Nat.cast_pow] using he'
  rw [he]
  exact hm

#print axioms CompactModelCoefficientBounds.selector_bounds
#print axioms CompactModelCoefficientBounds.copy_coefficient_bound
end CompactModelCoefficientBounds
