import DiophantineConsistency.ArithmeticCyclicWord
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace BandCarryInputs
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticCyclicWord ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_word_bound (q n u v : V) (hq : q=Exp.exp (67*n)) (hu : 0<u) :
    q-u-v < Exp.exp (67*n) := by
  rw [← hq]
  have hqpos : 0<q := by rw [hq]; exact exp_pos _
  exact lt_of_le_of_lt tsub_le_self (tsub_lt_self hqpos hu)

theorem aligned_rotation_bounds (n C e D : V) (hn : 0<n)
    (hC : C<Exp.exp (67*n)) (hcap : ∀ k<n, dig 67 C k≤D) :
    rot 67 n C (e%n) < Exp.exp (67*n) ∧
      ∀ k<n, dig 67 (rot 67 n C (e%n)) k≤D := by
  have he : e%n<n := mod_lt _ hn
  refine ⟨rot_lt 67 n C _ (le_of_lt he) hC, ?_⟩
  intro k hk
  rw [dig_rot 67 n C _ k he hk hC]
  exact hcap _ (cyc_lt hn k (e%n))

theorem residual_bounds (n T : V) (hM : 0<Exp.exp (67*n)-1) :
    T%(Exp.exp (67*n)-1)<Exp.exp (67*n) ∧
      ∀ k : V, dig 67 (T%(Exp.exp (67*n)-1)) k ≤ Exp.exp 67-1 := by
  constructor
  · exact lt_of_lt_of_le (mod_lt _ hM) tsub_le_self
  · intro k
    exact le_tsub_of_add_le_right (lt_iff_succ_le.mp (dig_lt 67 _ k))

theorem normalized_congruence (M A T F : V) (hM : 0<M)
    (h : (A+T)%M=F) : (A+T%M)%M=F := by
  rw [mod_add hM, mod_mod' _ hM, ← mod_add hM]
  exact h
#print axioms BandCarryInputs.source_word_bound
#print axioms BandCarryInputs.aligned_rotation_bounds
#print axioms BandCarryInputs.residual_bounds
#print axioms BandCarryInputs.normalized_congruence
end BandCarryInputs
