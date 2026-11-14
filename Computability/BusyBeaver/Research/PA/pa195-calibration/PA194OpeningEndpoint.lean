import PA194FreeMixed
import PA194OpeningHistory
import PA194InductionEndpoint
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace PA194OpeningEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194MixedVector PA194FreeMixed PA194OpeningHistory
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem opening_history_endpoint (p n s : V) (hp : IsSemiformula ℒₒᵣ n p)
    (hshift : shift ℒₒᵣ p = p)
    (hzero : znth s 0 = qqAlls p n)
    (hrec : ∀ i < n, znth s (i+1) = opener (znth s i)) :
    znth s n = subst ℒₒᵣ (fvarVec n) p := by
  have hd : 𝚺₁-Predicate (fun i : V => i ≤ n →
      znth s i = qqAlls (subst ℒₒᵣ (mixedVec (n-i) i) p) (n-i)) := by definability
  have hinv : ∀ i : V, i ≤ n →
      znth s i = qqAlls (subst ℒₒᵣ (mixedVec (n-i) i) p) (n-i) := by
    intro i
    induction i using ISigma1.sigma1_succ_induction
    · exact hd
    case zero =>
      intro _
      have hv : IsSemitermVec ℒₒᵣ n n (mixedVec n 0) := by simpa using (mixed_shape n 0).1
      have hs : subst ℒₒᵣ (mixedVec n 0) p = p := subst_eq_self hp hv (mixed_shape n 0).2.1
      simpa [hs] using hzero
    case succ i ih =>
      intro hi
      have hil : i < n := succ_le_iff_lt.mp hi
      have hni : n-i = (n-(i+1))+1 := by simpa using (sub_succ_add_succ hil (0 : V)).symm
      have hsum : (n-(i+1))+1+i = n := by rw [←hni]; exact tsub_add_cancel_of_le (le_of_lt hil)
      have hp' : IsSemiformula ℒₒᵣ ((n-(i+1))+1+i) p := by simpa [hsum] using hp
      rw [hrec i hil, ih (le_of_lt hil),hni,qqAlls_succ,opener_all,
        free_mixed_transition p (n-(i+1)) i hp' hshift]
  simpa [mixed_zero] using hinv n (le_refl n)
theorem induction_body_of_closure (p K n : V) (hp : IsSemiformula ℒₒᵣ n p)
    (hshift : shift ℒₒᵣ p = p) (hbv : bv ℒₒᵣ p = n)
    (hK : IsSemiformula ℒₒᵣ 1 K)
    (hdecode : subst ℒₒᵣ (fvarVec n) p = indBodyVal K) :
    Provable (𝗣𝗔 : ArithmeticTheory) (indBodyVal K) := by
  apply PA194InductionEndpoint.induction_body_model_length p K n hp hshift hbv hK hdecode
  intro s _ _ hzero hrec
  exact opening_history_endpoint p n s hp hshift hzero hrec
#print axioms induction_body_of_closure
#print axioms opening_history_endpoint
end PA194OpeningEndpoint
