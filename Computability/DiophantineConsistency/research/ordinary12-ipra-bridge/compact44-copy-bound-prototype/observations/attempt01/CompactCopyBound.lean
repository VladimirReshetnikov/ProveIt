import DiophantineConsistency.ArithmeticWindowDigits
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactCopyBound
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency.ArithmeticBinaryPopulation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem exp_nat_cast (n : ℕ) : Exp.exp (n:V)=(2:V)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add,Nat.cast_one,exp_succ,ih,pow_succ,mul_comm]

theorem copy_bound (bits : Fin 41 → V) (hb : ∀i,bits i≤1) :
    (∑ i,(2:V)^i.val*bits i)<Exp.exp 41 := by
  have hnat : (∑ i:Fin 41, (2:ℕ)^i.val)=2199023255551 := by decide
  have hsum : (∑ i:Fin 41,(2:V)^i.val)=2199023255551 := by
    have h := congrArg (fun n:ℕ => (n:V)) hnat
    norm_num only [Nat.cast_sum,Nat.cast_pow,Nat.cast_ofNat] at h
    exact h
  have hexp : Exp.exp (41:V)=2199023255552 := by
    have he := exp_nat_cast (V:=V) 41
    norm_num only [Nat.cast_ofNat] at he
    rw [he]
  calc
    _≤∑ i:Fin 41,(2:V)^i.val := by
      simpa only [mul_one] using Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hb i) (by simp : (0:V)≤(2:V)^i.val))
    _=2199023255551 := hsum
    _<Exp.exp 41 := by rw [hexp]; norm_num
theorem model_bit_copy_bound (X : V) (position : Fin 41 → V) :
    (∑ i,(2:V)^i.val*fbit X (position i))<Exp.exp 41 :=
  copy_bound _ (fun i => fbit_le_one X (position i))
end CompactCopyBound
#print axioms CompactCopyBound.copy_bound
#print axioms CompactCopyBound.model_bit_copy_bound
