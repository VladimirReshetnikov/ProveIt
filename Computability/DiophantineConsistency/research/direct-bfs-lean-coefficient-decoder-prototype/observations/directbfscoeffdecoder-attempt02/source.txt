import DirectBFSDecoder
import DirectBFSCoefficientMass
import DiophantineConsistency.ArithmeticWindowCarry
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectBFSCoefficientDecoder
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
    ((CompactCoefficientMass.value (DirectBFSSymbolicKernel.row i):ℕ):V) =
      DirectBFSDecoder.tileValue (V:=V) i := by
  simp only [CompactCoefficientMass.value, DirectBFSDecoder.tileValue,
    CompactTilePayload.value, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  norm_num

/-- Each *actual* finite selector coefficient has the decoder's model shape. -/
theorem selector_model (i : Fin 943) :
    ((CompactCoefficientMass.selector (DirectBFSSymbolicKernel.row i):ℕ):V) =
      1 + Exp.exp 10 * (Exp.exp 41 - DirectBFSDecoder.tileValue (V:=V) i) := by
  have hm : DirectBFSSymbolicKernel.row i ∈ DirectBFSSymbolicKernel.rows := by
    exact List.get_mem DirectBFSSymbolicKernel.rows _
  have hv := of_decide_eq_true ((List.all_eq_true.mp DirectBFSCoefficientMass.values_in_range)
    (DirectBFSSymbolicKernel.row i) hm)
  have hle : CompactCoefficientMass.value (DirectBFSSymbolicKernel.row i) ≤ 2^41 := le_of_lt hv.2
  have hsub : (((2^41 - CompactCoefficientMass.value (DirectBFSSymbolicKernel.row i):ℕ):V) +
      ((CompactCoefficientMass.value (DirectBFSSymbolicKernel.row i):ℕ):V)) = ((2^41:ℕ):V) := by
    exact_mod_cast (Nat.sub_add_cancel hle)
  have hleV : ((CompactCoefficientMass.value (DirectBFSSymbolicKernel.row i):ℕ):V) ≤ ((2^41:ℕ):V) := by
    exact_mod_cast hle
  have hsubV : (((2^41 - CompactCoefficientMass.value (DirectBFSSymbolicKernel.row i):ℕ):V)) =
      ((2^41:ℕ):V) - ((CompactCoefficientMass.value (DirectBFSSymbolicKernel.row i):ℕ):V) := by
    apply add_right_cancel (b := ((CompactCoefficientMass.value (DirectBFSSymbolicKernel.row i):ℕ):V))
    rw [hsub, tsub_add_cancel_of_le hleV]
  rw [CompactCoefficientMass.selector, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
    hsubV, cast_value]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have h10 : Exp.exp (10:V)=(2:V)^10 := by simpa only [Nat.cast_ofNat] using exp_nat_cast (V:=V) 10
  have h41 : Exp.exp (41:V)=(2:V)^41 := by simpa only [Nat.cast_ofNat] using exp_nat_cast (V:=V) 41
  rw [h10,h41]

/-- Local finite weighted sum; no assertion that it is a graph column. -/
theorem finite_decomposition (f : Fin 943 → V) (b : Fin 41 → V) :
    (∑ i, ((CompactCoefficientMass.selector (DirectBFSSymbolicKernel.row i):ℕ):V)*f i) +
      (∑ j, ((2^(10+j.val):ℕ):V)*b j) =
    (∑ i,f i) + Exp.exp 10 *
      ((∑ i,(Exp.exp 41-DirectBFSDecoder.tileValue (V:=V) i)*f i) +
       ∑ j,(2:V)^j.val*b j) := by
  simp_rw [selector_model, add_mul, one_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
  rw [Finset.sum_add_distrib]
  have h10 : Exp.exp (10:V)=(2:V)^10 := by simpa only [Nat.cast_ofNat] using exp_nat_cast (V:=V) 10
  simp only [h10]
  simp_rw [mul_assoc, mul_comm ((2:V)^10)]
  simp only [← Finset.sum_mul]
  ring

#print axioms DirectBFSCoefficientDecoder.cast_value
#print axioms DirectBFSCoefficientDecoder.selector_model
#print axioms DirectBFSCoefficientDecoder.finite_decomposition
end DirectBFSCoefficientDecoder
