import PA194QVecHistory
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194QVecDistribution
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem distribution (p s N : V) (hp : IsUFormula ℒₒᵣ p)
    (hrec : ∀ i < N, znth s (i+1) = qVec ℒₒᵣ (znth s i)) :
    ∀ k ≤ N, ∀ i ≤ N, i+k ≤ N →
      subst ℒₒᵣ (znth s i) (qqAlls p k) = qqAlls (subst ℒₒᵣ (znth s (i+k)) p) k := by
  have hd : 𝚺₁-Predicate (fun k : V => k ≤ N → ∀ i ≤ N, i+k ≤ N →
      subst ℒₒᵣ (znth s i) (qqAlls p k) = qqAlls (subst ℒₒᵣ (znth s (i+k)) p) k) := by
    definability
  intro k
  induction k using ISigma1.sigma1_succ_induction
  · exact hd
  case zero => intro _ i _ _; simp
  case succ k ih =>
    intro hk i hi hik
    have hki : k ≤ N := le_trans (le_of_lt (lt_add_one k)) hk
    have hi1sum : (i+1)+k ≤ N := by simpa [add_assoc,add_comm,add_left_comm] using hik
    have hi1le : i+1 ≤ N := le_trans (le_add_right (le_refl (i+1))) hi1sum
    have hil : i < N := succ_le_iff_lt.mp hi1le
    have heq := ih hki (i+1) hi1le hi1sum
    rw [qqAlls_succ,substs_all (isUFormula_qqAlls.mpr hp), ← hrec i hil, heq]
    simp [qqAlls_succ,add_assoc,add_comm,add_left_comm]
theorem subst_all_iter_exists (p w k : V) (hp : IsUFormula ℒₒᵣ p) :
    ∃ q, subst ℒₒᵣ w (qqAlls p k) = qqAlls q k := by
  obtain ⟨s,hseq,hlen,hzero,hrec⟩ := PA194QVecHistory.opening_history w k
  refine ⟨subst ℒₒᵣ (znth s k) p, ?_⟩
  have h := distribution p s k hp hrec k (le_refl k) 0 (zero_le) (by simp)
  simpa [hzero] using h

theorem shift_all_iter (p k : V) (hp : IsUFormula ℒₒᵣ p) :
    shift ℒₒᵣ (qqAlls p k) = qqAlls (shift ℒₒᵣ p) k := by
  have hd : 𝚺₁-Predicate (fun k : V => shift ℒₒᵣ (qqAlls p k) = qqAlls (shift ℒₒᵣ p) k) := by definability
  induction k using ISigma1.sigma1_succ_induction
  · exact hd
  case zero => simp
  case succ k ih => simp [qqAlls_succ, shift_all (isUFormula_qqAlls.mpr hp), ih]

theorem free_all_iter_exists (p k : V) (hp : IsUFormula ℒₒᵣ p) :
    ∃ q, free ℒₒᵣ (qqAlls p k) = qqAlls q k := by
  unfold free substs1
  rw [shift_all_iter p k hp]
  exact subst_all_iter_exists (shift ℒₒᵣ p) _ k hp.shift
#print axioms distribution
#print axioms subst_all_iter_exists
#print axioms shift_all_iter
#print axioms free_all_iter_exists
end PA194QVecDistribution
