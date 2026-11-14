import PA194IteratedFree
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194QVecHistory
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def opener (p : V) : V := qVec ℒₒᵣ p
noncomputable def openingBlueprint : PR.Blueprint 1 where
  zero := .mkSigma “z a. z = a”
  succ := .mkSigma “z r i a. !(qVecGraph ℒₒᵣ) z r”
noncomputable def openingConstruction : PR.Construction V openingBlueprint where
  zero := fun v => v 0
  succ := fun _ _ p => opener p
  zero_defined := .mk fun v => by simp [openingBlueprint]
  succ_defined := .mk fun v => by simp [openingBlueprint,opener,qVec.defined.iff]

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
#print axioms opening_history
end PA194QVecHistory
