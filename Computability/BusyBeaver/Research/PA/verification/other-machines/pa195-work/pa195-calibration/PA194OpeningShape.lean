import PA194OpeningHistory
import PA194QVecDistribution
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace PA194OpeningShape
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194OpeningHistory PA194QVecDistribution
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem history_shape (p n s : V) (hp : IsSemiformula ℒₒᵣ n p)
    (hzero : znth s 0 = qqAlls p n)
    (hrec : ∀ i < n, znth s (i+1) = opener (znth s i)) :
    ∀ i < n, ∃ q, IsSemiformula ℒₒᵣ 1 q ∧ znth s i = ^∀ q := by
  have hx : IsFormula ℒₒᵣ (qqAlls p n) := by
    have hh := IsSemiformula.qqAlls (n := (0 : V)) (k := n) (by simpa using hp)
    simpa using hh
  have hd : 𝚺₁-Predicate (fun i : V => i ≤ n → ∃ q, IsUFormula ℒₒᵣ q ∧
      IsFormula ℒₒᵣ (znth s i) ∧ znth s i = qqAlls q (n-i)) := by definability
  have hall : ∀ i : V, i ≤ n → ∃ q, IsUFormula ℒₒᵣ q ∧
      IsFormula ℒₒᵣ (znth s i) ∧ znth s i = qqAlls q (n-i) := by
    intro i
    induction i using ISigma1.sigma1_succ_induction
    · exact hd
    case zero =>
      intro _
      refine ⟨p,hp.isUFormula,?_,?_⟩
      · simpa [hzero] using hx
      · simpa using hzero
    case succ i ih =>
      intro hi1
      have hil : i < n := succ_le_iff_lt.mp hi1
      have hile : i ≤ n := le_of_lt hil
      obtain ⟨q,hq,hwf,hcur⟩ := ih hile
      have he : n-i = (n-(i+1))+1 := by simpa using (sub_succ_add_succ hil (0 : V)).symm
      have hcurall : znth s i = ^∀ (qqAlls q (n-(i+1))) := by rw [hcur,he,qqAlls_succ]
      have hbody : IsSemiformula ℒₒᵣ 1 (qqAlls q (n-(i+1))) := by
        have hxall : IsSemiformula ℒₒᵣ (0 : V) (^∀ (qqAlls q (n-(i+1)))) := by rw [←hcurall]; exact hwf
        simpa using (IsSemiformula.all.mp hxall)
      obtain ⟨q',hq'⟩ := free_all_iter_exists q (n-(i+1)) hq
      have hnext : znth s (i+1) = qqAlls q' (n-(i+1)) := by
        rw [hrec i hil,hcurall,opener_all,hq']
      have hnextwf : IsFormula ℒₒᵣ (znth s (i+1)) := by
        rw [hrec i hil,hcurall,opener_all]
        exact hbody.free
      have hqU : IsUFormula ℒₒᵣ q' := by
        have hU := hnextwf.isUFormula
        rw [hnext] at hU
        exact isUFormula_qqAlls.mp hU
      exact ⟨q',hqU,hnextwf,hnext⟩
  intro i hi
  obtain ⟨q,hq,hwf,hcur⟩ := hall i (le_of_lt hi)
  have he : n-i = (n-(i+1))+1 := by simpa using (sub_succ_add_succ hi (0 : V)).symm
  refine ⟨qqAlls q (n-(i+1)),?_,?_⟩
  · have hxall : IsSemiformula ℒₒᵣ (0 : V) (^∀ (qqAlls q (n-(i+1)))) := by
      rw [←qqAlls_succ, ←he, ←hcur]
      exact hwf
    simpa using (IsSemiformula.all.mp hxall)
  · rw [hcur,he,qqAlls_succ]
theorem open_block_provable (p n : V) (hp : IsSemiformula ℒₒᵣ n p)
    (hseed : Provable (𝗣𝗔 : ArithmeticTheory) (qqAlls p n)) :
    ∃ s, Seq s ∧ lh s = n+1 ∧ znth s 0 = qqAlls p n ∧
      (∀ i < n, znth s (i+1) = opener (znth s i)) ∧
      (∀ i < n+1, Provable (𝗣𝗔 : ArithmeticTheory) (znth s i)) := by
  obtain ⟨s,hseq,hlen,hzero,hrec,hsound⟩ := opening_history_exists_sound (qqAlls p n) n hseed
  refine ⟨s,hseq,hlen,hzero,hrec,hsound ?_⟩
  exact history_shape p n s hp hzero hrec
#print axioms open_block_provable
#print axioms history_shape
end PA194OpeningShape
