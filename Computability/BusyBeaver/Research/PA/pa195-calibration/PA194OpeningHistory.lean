import PA194IteratedFree
set_option autoImplicit false
set_option maxHeartbeats 1000000
/-! Model-length history for the concrete universal opener. -/
namespace PA194OpeningHistory
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def opener (p : V) : V := free ℒₒᵣ (sndIdx p)
noncomputable def openingBlueprint : PR.Blueprint 1 where
  zero := .mkSigma “z a. z = a”
  succ := .mkSigma “z r i a. ∃ u, !sndIdxDef u r ∧ !(freeGraph ℒₒᵣ) z u”
noncomputable def openingConstruction : PR.Construction V openingBlueprint where
  zero := fun v => v 0
  succ := fun _ _ p => opener p
  zero_defined := .mk fun v => by simp [openingBlueprint]
  succ_defined := .mk fun v => by simp [openingBlueprint,opener,sndIdx_defined.iff,free.defined.iff]

theorem opening_history (x n : V) :
    ∃ s, Seq s ∧ lh s = n+1 ∧ znth s 0 = x ∧ ∀ i < n, znth s (i+1) = opener (znth s i) := by
  let c := openingConstruction (V := V)
  obtain ⟨s,hs,hlen⟩ := PR.Construction.CSeq.exists c ![x] n
  have hzero : znth s 0 = x := by
    have hm : ⟪(0 : V),x⟫ ∈ s := by simpa [c,openingConstruction] using hs.zero
    exact hs.seq.znth_eq_of_mem hm
  refine ⟨s,hs.seq,hlen.symm,hzero,?_⟩
  intro i hi
  have himem : ⟪i,znth s i⟫ ∈ s := hs.seq.znth (by rw [←hlen]; exact lt_trans hi (lt_add_one _))
  have hnextmem := hs.succ i (by rw [←hlen]; simpa using hi) (znth s i) himem
  have hn : i+1 < lh s := by rw [←hlen]; simpa [add_comm] using add_lt_add_right hi 1
  have hactual := hs.seq.znth hn
  exact hs.seq.isMapping.uniq hactual (by simpa [c,openingConstruction] using hnextmem)
@[simp] lemma opener_all (p : V) : opener (^∀ p) = free ℒₒᵣ p := by
  simp [opener,sndIdx,qqAll]

theorem opening_history_sound (s n : V)
    (hlen : lh s = n+1)
    (hseed : Provable (𝗣𝗔 : ArithmeticTheory) (znth s 0))
    (hrec : ∀ i < n, znth s (i+1) = opener (znth s i))
    (hshape : ∀ i < n, ∃ p, IsSemiformula ℒₒᵣ 1 p ∧ znth s i = ^∀ p) :
    ∀ i < n+1, Provable (𝗣𝗔 : ArithmeticTheory) (znth s i) := by
  have hdef : 𝚺₁-Predicate (fun k : V => ∀ i < k, i < n+1 → Provable (𝗣𝗔 : ArithmeticTheory) (znth s i)) := by
    definability
  have hall : ∀ k : V, ∀ i < k, i < n+1 → Provable (𝗣𝗔 : ArithmeticTheory) (znth s i) := by
    intro k
    induction k using ISigma1.sigma1_succ_induction
    · exact hdef
    case zero => intro i hi; exact False.elim (not_lt_zero hi)
    case succ k ih =>
      intro i hi hil
      by_cases hlt : i < k
      · exact ih i hlt hil
      · have hieq : i = k := le_antisymm (lt_succ_iff_le.mp hi) (le_of_not_gt hlt)
        subst i
        rcases zero_or_succ k with (rfl | ⟨j,rfl⟩)
        · exact hseed
        · have hj : j < n := (add_lt_add_iff_right 1).mp hil
          obtain ⟨p,hp,hprev⟩ := hshape j hj
          have hj' : j < j+1 := lt_add_one j
          have hjbound : j < n+1 := lt_trans hj (lt_add_one n)
          have hprevproof := ih j hj' hjbound
          rw [hprev] at hprevproof
          rw [hrec j hj,hprev,opener_all]
          exact PA194IteratedFree.free_of_all hp hprevproof
  intro i hi
  exact hall (n+1) i hi hi
theorem opening_history_exists_sound (x n : V)
    (hseed : Provable (𝗣𝗔 : ArithmeticTheory) x) :
    ∃ s, Seq s ∧ lh s = n+1 ∧ znth s 0 = x ∧
      (∀ i < n, znth s (i+1) = opener (znth s i)) ∧
      ((∀ i < n, ∃ p, IsSemiformula ℒₒᵣ 1 p ∧ znth s i = ^∀ p) →
        ∀ i < n+1, Provable (𝗣𝗔 : ArithmeticTheory) (znth s i)) := by
  obtain ⟨s,hseq,hlen,h0,hrec⟩ := opening_history x n
  refine ⟨s,hseq,hlen,h0,hrec,?_⟩
  intro hshape
  apply opening_history_sound s n hlen ?_ hrec hshape
  simpa [h0] using hseed
#print axioms opening_history_exists_sound
#print axioms opening_history
#print axioms opening_history_sound
end PA194OpeningHistory
