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
      simpa only [one_mul,Nat.cast_pow,Nat.cast_ofNat] using (cast_exp (V:=V) m)
    rw [hp] at hs
    simpa only [Finset.sum_range_succ,Nat.cast_succ] using hs

theorem bit (m : ℕ) (bits : Fin m → V) (hb : ∀ j, bits j≤1) (j : Fin m) :
    fbit (∑ i : Fin m, (2:V)^i.val*bits i) (j.val:V)=bits j := by
  classical
  let f : V → V := fun x => ∑ i : Fin m, if x=(i.val:V) then bits i else 0
  have hf (i : Fin m) : f (i.val:V)=bits i := by
    unfold f
    apply Finset.sum_eq_single i
    · intro j _ hne
      have hcast : (i.val:V)≠(j.val:V) := by
        intro h
        have hv : i.val=j.val := by exact_mod_cast h
        exact hne (Fin.ext hv.symm)
      simp [hcast]
    · intro hn
      exact False.elim (hn (Finset.mem_univ i))
    · simp
  have hbound : ∀ j : ℕ, j<m → f (j:V)≤1 := by
    intro j hj
    simpa only [hf ⟨j,hj⟩] using hb ⟨j,hj⟩
  have hs := finite_blocks f m hbound
  have he : (∑ j ∈ Finset.range m, f (j:V)*(2:V)^j) = ∑ i : Fin m, (2:V)^i.val*bits i := by
    rw [Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hjm : j<m := Finset.mem_range.mp hj
    rw [hf ⟨j,hjm⟩]
    exact mul_comm _ _
  rw [he] at hs
  have hj : (j.val:V)<(m:V) := by exact_mod_cast j.isLt
  have hd := hs.2 (j.val:V) hj
  rw [hf j] at hd
  have hbit := dig_eq_fbit 1 (∑ i : Fin m, (2:V)^i.val*bits i) (j.val:V) (by norm_num) (by rw [hd]; exact hb j)
  simpa only [one_mul,hd] using hbit.symm
#print axioms FiniteBinaryWord.finite_blocks
#print axioms FiniteBinaryWord.bit
end FiniteBinaryWord
