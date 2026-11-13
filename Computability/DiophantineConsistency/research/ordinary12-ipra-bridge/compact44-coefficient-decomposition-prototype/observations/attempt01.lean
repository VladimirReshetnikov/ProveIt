import DiophantineConsistency.Compact943Decoder
import DiophantineConsistency.CompactCoefficientMass
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactCoefficientDecoder
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency.ArithmeticBinaryCarry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem exp_nat_cast (n : ℕ) : Exp.exp (n:V)=(2:V)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add,Nat.cast_one,exp_succ,ih,pow_succ,mul_comm]

/-- The table's natural payload is the same expression in an arithmetic model. -/
theorem cast_value (i : Fin 943) :
    ((CompactCoefficientMass.value (Compact943Data.row i):ℕ):V) =
      Compact943Decoder.tileValue (V:=V) i := by
  simp only [CompactCoefficientMass.value, Compact943Decoder.tileValue,
    CompactTilePayload.value, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  norm_num

/-- Each *actual* finite selector coefficient has the decoder's model shape. -/
theorem selector_model (i : Fin 943) :
    ((CompactCoefficientMass.selector (Compact943Data.row i):ℕ):V) =
      1 + Exp.exp 10 * (Exp.exp 41 - Compact943Decoder.tileValue (V:=V) i) := by
  have hm : Compact943Data.row i ∈ Compact943Data.rows := by
    exact List.get_mem Compact943Data.rows _
  have hv := of_decide_eq_true ((List.all_eq_true.mp CompactCoefficientMass.values_in_range)
    (Compact943Data.row i) hm)
  have hle : CompactCoefficientMass.value (Compact943Data.row i) ≤ 2^41 := le_of_lt hv.2
  rw [CompactCoefficientMass.selector, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
    Nat.cast_sub hle, cast_value]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [exp_nat_cast (V:=V) 10, exp_nat_cast (V:=V) 41]

/-- Local finite weighted sum; no assertion that it is a graph column. -/
theorem finite_decomposition (f : Fin 943 → V) (b : Fin 41 → V) :
    (∑ i, ((CompactCoefficientMass.selector (Compact943Data.row i):ℕ):V)*f i) +
      (∑ j, ((2^(10+j.val):ℕ):V)*b j) =
    (∑ i,f i) + Exp.exp 10 *
      ((∑ i,(Exp.exp 41-Compact943Decoder.tileValue (V:=V) i)*f i) +
       ∑ j,(2:V)^j.val*b j) := by
  simp_rw [selector_model, add_mul, one_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
  rw [Finset.sum_add_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [exp_nat_cast (V:=V) 10]
  ring

#print axioms CompactCoefficientDecoder.cast_value
#print axioms CompactCoefficientDecoder.selector_model
#print axioms CompactCoefficientDecoder.finite_decomposition
end CompactCoefficientDecoder
