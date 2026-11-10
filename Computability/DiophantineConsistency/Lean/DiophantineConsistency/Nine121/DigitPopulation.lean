import DiophantineConsistency.ModelDigitTransfer

/-! # Populations of radix-`2^v` digit sums, in every model of `𝗜𝚺₁`

* `population_dsum`: for digits below `B = 2^v`, the binary weight of
  `Σ_{i<n} fᵢ Bⁱ` is `Σ_{i<n} σ(fᵢ)` (concatenation, `ArithmeticBinaryPopulation.concatenate`);
* `population_exp_sub_exp`: `σ(2^v − 2^k) = v − k` for `k ≤ v`;

These give the populations of the low code mask (`B − b` at the code positions,
`B − 1` elsewhere) and of the high target mask (`B − 2` at the targets) that
calibrate the sparse central binomial test (`SparseCentral`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Nine121.DigitPopulation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryPopulation ModelDigitTransfer ModelCarries
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem population_zero : population (0 : V) = 0 := by
  have h := ArithmeticBinaryPopulation.complement (0 : V) 0 (by simp)
  have h2 := population_exp_sub_one (0 : V)
  rw [exp_zero] at h h2
  simpa using h

theorem population_dsum (v : V) (f : ℕ → V) (n : ℕ) (hf : ∀ i < n, f i < Exp.exp v) :
    population (dsum (Exp.exp v) f n) = ∑ i ∈ Finset.range n, population (f i) := by
  induction n with
  | zero => rw [dsum_zero, Finset.sum_range_zero, population_zero]
  | succ n ih =>
    have hf' : ∀ i < n, f i < Exp.exp v := fun i hi => hf i (Nat.lt_succ_of_lt hi)
    obtain ⟨K, hK⟩ := pow_exp_exists v n
    have hlt : dsum (Exp.exp v) f n < Exp.exp K := by rw [← hK]; exact dsum_lt _ f n hf'
    rw [dsum_succ, Finset.sum_range_succ, ← ih hf', hK, add_comm,
      ArithmeticBinaryPopulation.concatenate _ _ _ hlt, add_comm]

theorem population_exp_sub_exp {k v : V} (hkv : k ≤ v) :
    population (Exp.exp v - Exp.exp k) = v - k := by
  have e : Exp.exp v - Exp.exp k = (Exp.exp (v - k) - 1) * Exp.exp k + 0 := by
    have h1 : Exp.exp v = Exp.exp (v - k) * Exp.exp k := by rw [← exp_add, tsub_add_cancel_of_le hkv]
    have h2 : 1 ≤ Exp.exp (v - k) := one_le_exp _
    rw [h1, add_zero]
    obtain ⟨a, ha⟩ : ∃ a, Exp.exp (v - k) = a + 1 := ⟨Exp.exp (v - k) - 1, (tsub_add_cancel_of_le h2).symm⟩
    rw [ha, add_tsub_cancel_right]
    rw [show (a + 1) * Exp.exp k = a * Exp.exp k + Exp.exp k by ring, add_tsub_cancel_right]
  rw [e, ArithmeticBinaryPopulation.concatenate _ _ _ (exp_pos k), population_zero, add_zero,
    population_exp_sub_one]

end Nine121.DigitPopulation

#print axioms Nine121.DigitPopulation.population_dsum
#print axioms Nine121.DigitPopulation.population_exp_sub_exp
