import DiophantineConsistency.ArithmeticWindowDigits
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactDigitBound
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency.ArithmeticRepunit
open DiophantineConsistency.ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Bounded digits give a scaled repunit bound; unlike the existing Boolean
case this permits any explicit digit bound, including the compact44 dummy 3. -/
theorem mod_le_scaled_rep (w X D k : V) :
    (∀ i<k,dig w X i≤D) → X%Exp.exp (w*k)≤D*rep w k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro _; simp
  case succ k ih =>
    intro h
    rw [mod_exp_succ,rep_succ_add,mul_add]
    exact add_le_add (ih fun i hi => h i (lt_trans hi (lt_add_one k)))
      (mul_le_mul_of_nonneg_right (h k (lt_add_one k)) (by simp))
/-- A finite standard family with digits bounded by D has its weighted low
remainder bounded by the scaled coefficient mass times the repunit. -/
theorem sum_mod_le_scaled {ι : Type*} [Fintype ι] (w n D k : V)
    (a X : ι → V) (hk : k ≤ n)
    (h : ∀ i, ∀ j < n, dig w (X i) j ≤ D) :
    (∑ i, a i * (X i % Exp.exp (w*k))) ≤ ((∑ i, a i) * D) * rep w k := by
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have hi := mod_le_scaled_rep w (X i) D k
    (fun j hj => h i j (lt_of_lt_of_le hj hk))
  calc
    a i * (X i % Exp.exp (w*k)) ≤ a i * (D * rep w k) :=
      mul_le_mul_of_nonneg_left hi (by simp)
    _ = (a i * D) * rep w k := by ring
/-- Bound a single weighted column without assuming Boolean digits. -/
theorem raw_le_scaled {ι : Type*} [Fintype ι] (w D k : V)
    (a X : ι → V) (h : ∀ i, dig w (X i) k ≤ D) :
    (∑ i, a i * dig w (X i) k) ≤ (∑ i, a i) * D := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (by simp)
/-- A column whose raw value plus the known carry bound is below the radix
has zero outgoing carry. The caller must establish the bound for this column. -/
theorem clean_outgoing (radix raw incoming bound outgoing : V)
    (hin : incoming ≤ bound) (hsmall : raw + bound < radix)
    (hquot : outgoing = (raw + incoming) / radix) : outgoing = 0 := by
  rw [hquot]
  exact div_eq_zero_of_lt _ (lt_of_le_of_lt (add_le_add_left hin raw) hsmall)

/-- When the incoming carry is zero, a column identity with zero outgoing
carry identifies its output digit with its raw sum. -/
theorem clean_column (radix raw incoming outgoing digit : V)
    (hin : incoming = 0) (hout : outgoing = 0)
    (hcolumn : raw + incoming = digit + radix * outgoing) : digit = raw := by
  simpa [hin, hout] using hcolumn.symm
/-- Arithmetic bound needed by an end-around carry argument with digit cap D. -/
theorem scaled_key_bound (w D mass bound k : V)
    (hmass : mass * D + 1 ≤ (bound+1) * (Exp.exp w - 1)) :
    (mass * D) * rep w k + rep w k + (bound+1) ≤
      (bound+1) * Exp.exp (w*k) := by
  have hu := repunit_identity w k
  have hm := mul_le_mul_of_nonneg_right hmass (by simp : (0:V) ≤ rep w k)
  calc
    (mass * D) * rep w k + rep w k + (bound+1) =
        (mass * D + 1) * rep w k + (bound+1) := by ring
    _ ≤ (bound+1) * (Exp.exp w - 1) * rep w k + (bound+1) :=
      (add_le_add_iff_right _).mpr hm
    _ = (bound+1) * ((Exp.exp w - 1) * rep w k + 1) := by ring
    _ = (bound+1) * Exp.exp (w*k) := by rw [hu]
end CompactDigitBound
#print axioms CompactDigitBound.scaled_key_bound
#print axioms CompactDigitBound.clean_outgoing
#print axioms CompactDigitBound.clean_column
#print axioms CompactDigitBound.raw_le_scaled
#print axioms CompactDigitBound.sum_mod_le_scaled
#print axioms CompactDigitBound.mod_le_scaled_rep
