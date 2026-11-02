import DiophantineConsistency.FixedGraphAllBlockWord
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteBinaryWord
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticPackingBlocks ArithmeticStandardCasts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem finite_blocks (f : V → V) (m : ℕ) (hb : ∀ j : ℕ, j<m → f (j:V)≤1) :
    Blocks 1 f (m:V) (∑ j ∈ Finset.range m, f (j:V)*(2:V)^j) := by
  induction m with
  | zero => simpa using (blocks_zero (1:V) f)
  | succ m ih =>
    have hh := ih (fun j hj => hb j (Nat.lt_succ_of_lt hj))
    have hf : f (m:V)<Exp.exp (1:V) := by
      have h := hb m (Nat.lt_succ_self m)
      rw [exp_one]
      exact lt_of_le_of_lt h (by norm_num)
    have hs := blocks_succ hh hf
    have hp : Exp.exp ((1:V)*(m:V))=(2:V)^m := by
      simpa only [one_mul] using (cast_exp (V:=V) m).symm
    rw [hp] at hs
    simpa only [Finset.sum_range_succ,Nat.cast_succ] using hs

#print axioms FiniteBinaryWord.finite_blocks
end FiniteBinaryWord
