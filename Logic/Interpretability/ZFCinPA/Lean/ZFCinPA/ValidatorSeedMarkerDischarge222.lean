import ZFCinPA.ValidatorSeedSourceBasis222
import BoundedPAConsistency.InternalRelativization

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Eliminate an internally sized family of domain side formulas while
moving its free marker with the eigenvariable shift. The premise is an
actual seed-theory derivation; arbitrary source-proof interpretation is
a separate obligation. -/
namespace LeanProofs.ZFCinPA.ValidatorSeedMarkerDischarge222
open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open scoped LO.FirstOrder.Arithmetic
open ValidatorFullSeedTheory222 ValidatorSeedSourceBasis222
open LeanProofs.BoundedPAConsistency.InternalRelativization
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def memberCode (t u : V) : V := ^rel 2 1 ?[t,u]
def domainCode (j : V) : V := memberCode (^&j) (^#0)
def emptyCode (j : V) : V := ^∀ (Bootstrapping.imp ℒₛₑₜ (memberCode (^#0) (^&j)) (^⊥))
def memberGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out t u. ∃ tail vec, !adjoinDef tail u 0 ∧ !adjoinDef vec t tail ∧ !qqRelDef out 2 1 vec”
def domainGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out j. ∃ t z, !qqFvarDef t j ∧ !qqBvarDef z 0 ∧ !memberGraph out t z”
def emptyGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out j. ∃ t z p bot q, !qqFvarDef t j ∧ !qqBvarDef z 0 ∧
    !memberGraph p z t ∧ !qqFalsumDef bot ∧ !(Bootstrapping.impGraph ℒₛₑₜ) q p bot ∧ !qqAllDef out q”
instance member_defined : 𝚺₁-Function₂[V] memberCode via memberGraph :=
  .mk fun v => by simp [memberGraph,memberCode]
instance domain_defined : 𝚺₁-Function₁[V] domainCode via domainGraph :=
  .mk fun v => by simp [domainGraph,domainCode]
instance empty_defined : 𝚺₁-Function₁[V] emptyCode via emptyGraph :=
  .mk fun v => by simp [emptyGraph,emptyCode]

private theorem member_binding {n : ℕ} (t u : Semiterm V ℒₛₑₜ n) :
    (memTerm t u).val=memberCode t.val u.val := by
  simp [memTerm,memberCode]
  change ((1:ℕ):V)=1
  simp
theorem domain_binding (j : V) :
    (tagBody (Bootstrapping.Semiterm.fvar j : Term V ℒₛₑₜ)).val=domainCode j := by
  simp [tagBody,member_binding,domainCode]
theorem empty_binding (j : V) :
    (emptyAt (Bootstrapping.Semiterm.fvar j : Term V ℒₛₑₜ)).val=emptyCode j := by
  simp [emptyAt,member_binding,emptyCode]
theorem domain_typed (j : V) : IsSemiformula ℒₛₑₜ 1 (domainCode j) := by
  rw [←domain_binding]
  simpa only [Nat.cast_one] using (tagBody (Bootstrapping.Semiterm.fvar j)).isSemiformula
theorem empty_typed (j : V) : IsFormula ℒₛₑₜ (emptyCode j) := by
  rw [←empty_binding]
  exact (emptyAt (Bootstrapping.Semiterm.fvar j)).isSemiformula

theorem shift_domain (j : V) : shift ℒₛₑₜ (domainCode j)=domainCode (j+1) := by
  rw [←domain_binding,←domain_binding,←Bootstrapping.Semiformula.val_shift]
  congr 1
  simp [tagBody,memTerm]
theorem shift_empty (j : V) : shift ℒₛₑₜ (emptyCode j)=emptyCode (j+1) := by
  rw [←empty_binding,←empty_binding,←Bootstrapping.Semiformula.val_shift]
  congr 1
  simp [emptyAt,memTerm]

def sideSet (j : V) : V := domSet ℒₛₑₜ (domainCode j) j
def residual (j : V) : V := insert (^⊥) (insert (Bootstrapping.neg ℒₛₑₜ (emptyCode j)) (sideSet j))
instance sideSet_definable : 𝚺₁-Function₁[V] sideSet := by
  unfold sideSet; definability
instance residual_definable : 𝚺₁-Function₁[V] residual := by
  unfold residual; definability
theorem residual_typed (j : V) : IsFormulaSet ℒₛₑₜ (residual j) := by
  simp [residual,sideSet,empty_typed,isFormulaSet_domSet (domain_typed j)]
theorem sideSet_zero : sideSet (0:V)=∅ :=
  mem_ext fun y => by simp [sideSet,mem_domSet_iff]

theorem shift_domain_instance (j i : V) :
    shift ℒₛₑₜ (domF ℒₛₑₜ (domainCode j) i)=domF ℒₛₑₜ (domainCode (j+1)) (i+1) := by
  simp only [domF]
  rw [shift_neg ((domain_typed j).substs1 (show IsSemiterm ℒₛₑₜ 0 (^&i : V) by simp))]
  simp only [substs1]
  rw [shift_substs (domain_typed j) (show IsSemitermVec ℒₛₑₜ 1 0 ?[(^&i : V)] by simp),shift_domain]
  simp
theorem free_negative_domain (j : V) :
    free ℒₛₑₜ (Bootstrapping.neg ℒₛₑₜ (domainCode j))=domF ℒₛₑₜ (domainCode (j+1)) 0 := by
  simp only [free,domF]
  rw [shift_neg (domain_typed j),shift_domain]
  simp only [substs1]
  rw [substs_neg (domain_typed (j+1)) (show IsSemitermVec ℒₛₑₜ 1 0 ?[(^&0 : V)] by simp)]

theorem sideSet_succ (j : V) : sideSet (j+1)=
    insert (free ℒₛₑₜ (Bootstrapping.neg ℒₛₑₜ (domainCode j))) (setShift ℒₛₑₜ (sideSet j)) := by
  rw [free_negative_domain]
  apply mem_ext; intro y
  constructor
  · intro hy
    obtain ⟨i,hi,rfl⟩ := mem_domSet_iff.mp hy
    rcases zero_or_succ i with rfl | ⟨k,rfl⟩
    · simp
    · refine mem_bitInsert_iff.mpr (Or.inr (mem_setShift_iff.mpr ⟨domF ℒₛₑₜ (domainCode j) k,?_,?_⟩))
      · exact domF_mem_domSet (by simpa using hi)
      · exact (shift_domain_instance j k).symm
  · intro hy
    rcases mem_bitInsert_iff.mp hy with rfl | hy
    · exact domF_mem_domSet (by simp)
    · obtain ⟨z,hz,rfl⟩ := mem_setShift_iff.mp hy
      obtain ⟨i,hi,rfl⟩ := mem_domSet_iff.mp hz
      rw [shift_domain_instance]
      exact domF_mem_domSet (by simpa using hi)

theorem residual_succ (j : V) : residual (j+1)=
    insert (free ℒₛₑₜ (Bootstrapping.neg ℒₛₑₜ (domainCode j))) (setShift ℒₛₑₜ (residual j)) := by
  simp only [residual,sideSet_succ,mem_setShift_insert,shift_falsum,
    shift_neg (empty_typed j),shift_empty]
  apply mem_ext; intro y
  simp only [mem_bitInsert_iff]
  tauto

theorem tag_nonempty_provable (j : V) : Provable seedTheory (^∃ domainCode j) := by
  simpa only [Bootstrapping.Semiformula.val_exs,domain_binding] using
    (tprovable_iff_provable.mp (tagged_nonempty (Bootstrapping.Semiterm.fvar j : Term V ℒₛₑₜ)))

private theorem insert_provable {p Γ : V} (hΓ : IsFormulaSet ℒₛₑₜ (insert p Γ))
    (hp : Provable seedTheory p) : Derivable seedTheory (insert p Γ) := by
  refine Derivable.wk hΓ ?_ hp.toDerivable
  intro y hy
  rcases mem_bitInsert_iff.mp hy with rfl | hy
  · simp
  · simp at hy

/-- Remove one side formula, changing the marker from j+1 to j. -/
theorem discharge_succ (j : V) (h : Derivable seedTheory (residual (j+1))) :
    Derivable seedTheory (residual j) := by
  rw [residual_succ] at h
  have hall := Derivable.all (domain_typed j).neg h
  have hex : Derivable seedTheory (insert (^∃ domainCode j) (residual j)) :=
    insert_provable (by simp [domain_typed,residual_typed]) (tag_nonempty_provable j)
  refine Derivable.cut (^∀ (Bootstrapping.neg ℒₛₑₜ (domainCode j))) hall ?_
  rw [neg_all (domain_typed j).isUFormula.neg,(domain_typed j).isUFormula.neg_neg]
  exact hex

theorem discharge_all (N : V) (h : Derivable seedTheory (residual N)) :
    Derivable seedTheory (residual (0:V)) := by
  have key : ∀ k≤N, ∃ j, j+k=N ∧ Derivable seedTheory (residual j) := by
    intro k
    induction k using ISigma1.sigma1_succ_induction
    · definability
    · intro _; exact ⟨N,by simp,h⟩
    · case succ k ih =>
      intro hk
      obtain ⟨j,hj,hder⟩ := ih (le_trans (by simp) hk)
      rcases zero_or_succ j with rfl | ⟨j',rfl⟩
      · exfalso; simp [←hj] at hk
      · refine ⟨j',?_,discharge_succ j' hder⟩
        rw [←hj,add_comm k 1,←add_assoc]
  obtain ⟨j,hj,hder⟩ := key N le_rfl
  have hj0 : j=0 := by simpa using hj
  simpa only [hj0] using hder

private theorem empty_free_negative :
    free ℒₛₑₜ (Bootstrapping.neg ℒₛₑₜ (emptyBody : Semiformula V ℒₛₑₜ 1).val)=
      Bootstrapping.neg ℒₛₑₜ (emptyCode 0) := by
  have hp : IsSemiformula ℒₛₑₜ 1 (emptyBody : Semiformula V ℒₛₑₜ 1).val := by
    simpa only [Nat.cast_one] using (emptyBody : Semiformula V ℒₛₑₜ 1).isSemiformula
  simp only [free,substs1]
  rw [shift_neg hp,substs_neg hp.shift (show IsSemitermVec ℒₛₑₜ 1 0 ?[(^&(0:V) : V)] by simp)]
  congr 1
  change (emptyBody : Semiformula V ℒₛₑₜ 1).free.val=emptyCode 0
  rw [emptyBody_free,empty_binding]

theorem empty_object_provable :
    Provable seedTheory (^∃ (emptyBody : Semiformula V ℒₛₑₜ 1).val) := by
  simpa only [Bootstrapping.Semiformula.val_exs] using
    (tprovable_iff_provable.mp (empty_object (V:=V)))

/-- The source empty-object proof removes the final negative marker guard. -/
theorem discharge_zero (h : Derivable seedTheory (residual (0:V))) :
    Provable seedTheory (^⊥ : V) := by
  have h' : Derivable seedTheory
      (insert (free ℒₛₑₜ (Bootstrapping.neg ℒₛₑₜ (emptyBody : Semiformula V ℒₛₑₜ 1).val))
        (setShift ℒₛₑₜ (insert (^⊥) (∅ : V)))) := by
    rw [empty_free_negative]
    refine Derivable.ofSetEq (fun x => ?_) h
    simp [residual,sideSet_zero,mem_setShift_iff]
    tauto
  have hb : IsSemiformula ℒₛₑₜ 1 (emptyBody : Semiformula V ℒₛₑₜ 1).val := by
    simpa only [Nat.cast_one] using (emptyBody : Semiformula V ℒₛₑₜ 1).isSemiformula
  have hall := Derivable.all hb.neg h'
  have hex : Derivable seedTheory
      (insert (^∃ (emptyBody : Semiformula V ℒₛₑₜ 1).val) (insert (^⊥) (∅ : V))) :=
    insert_provable (by simp) empty_object_provable
  apply Derivable.toProvable
  refine Derivable.cut (^∀ (Bootstrapping.neg ℒₛₑₜ (emptyBody : Semiformula V ℒₛₑₜ 1).val)) hall ?_
  rw [neg_all (emptyBody : Semiformula V ℒₛₑₜ 1).isSemiformula.isUFormula.neg,
    (emptyBody : Semiformula V ℒₛₑₜ 1).isSemiformula.isUFormula.neg_neg]
  exact hex

/-- Conditional elimination for every internal counter, including zero. -/
theorem provable_falsum_of_residual (N : V) (h : Derivable seedTheory (residual N)) :
    Provable seedTheory (^⊥ : V) := discharge_zero (discharge_all N h)

end LeanProofs.ZFCinPA.ValidatorSeedMarkerDischarge222
