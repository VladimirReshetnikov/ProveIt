import PA194TargetReplay
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194TargetVectorJoin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194TargetCantor PA194TargetLeaves
 PA194TargetStep PA194TargetSound PA194TargetExtendedStep PA194ParamHistory PA194StackCode PA194StackHistory
 PA194TargetGuardedHistory PA194TargetVectorLength PA194TargetProofLeaf PA194TargetGeneralize PA194TargetReplay
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def Joined (p q z : M) : Prop := len z = len p + len q ∧
    (∀ i < len p, z.[i] = p.[i]) ∧ (∀ j < len q, z.[len p+j] = q.[j])

theorem selector_def (p q : M) : 𝚺₁-Relation (fun i y : M =>
    (i < len p ∧ y = p.[i]) ∨ ∃ j < len q, i = len p+j ∧ y = q.[j]) := by
  definability

theorem joined_exists (p q : M) : ∃ z, Joined p q z := by
  let R : M → M → Prop := fun i y =>
    (i < len p ∧ y = p.[i]) ∨ ∃ j < len q, i = len p+j ∧ y = q.[j]
  have hR : 𝚺₁-Relation R := selector_def p q
  have htotal : ∀ i < len p + len q, ∃ y, R i y := by
    intro i hi
    by_cases hp : i < len p
    · exact ⟨p.[i],Or.inl ⟨hp,rfl⟩⟩
    · have hle : len p ≤ i := le_of_not_gt hp
      obtain ⟨j,hj⟩ := le_iff_exists_add.mp hle
      have hjlt : j < len q := by
        have hh : len p+j < len p+len q := by simpa [hj] using hi
        exact (add_lt_add_iff_left (len p)).mp hh
      exact ⟨q.[j],Or.inr ⟨j,hjlt,hj,rfl⟩⟩
  obtain ⟨z,hzlen,hz⟩ := sigmaOne_skolem_vec hR htotal
  refine ⟨z,hzlen,?_,?_⟩
  · intro i hi
    have hlt : i < len p+len q := lt_of_lt_of_le hi (le_self_add : len p ≤ len p+len q)
    rcases hz i hlt with hleft | ⟨j,hj,hij,hy⟩
    · exact hleft.2
    · have hnot : ¬ i < len p := by rw [hij]; exact not_lt_of_ge (le_self_add : len p ≤ len p+j)
      exact False.elim (hnot hi)
  · intro j hj
    have hlt : len p+j < len p+len q := (add_lt_add_iff_left (len p)).mpr hj
    rcases hz (len p+j) hlt with hleft | ⟨j',hj',heq,hy⟩
    · exact False.elim ((not_lt_of_ge (le_self_add : len p ≤ len p+j)) hleft.1)
    · have hjeq : j = j' := add_left_cancel heq
      simpa [hjeq] using hy

theorem joined_prefix (p q z n : M) (hj : Joined p q z) (hn : n ≤ len p) :
    F autoHistory ![n,z,0] = F autoHistory ![n,p,0] := by
  have hf : 𝚺₁-Function₁ (fun k : M => F autoHistory ![k,z,0]) :=
    PA194CodeInstance.unary_of_three autoHistory z 0
  have hg : 𝚺₁-Function₁ (fun k : M => F autoHistory ![k,p,0]) :=
    PA194CodeInstance.unary_of_three autoHistory p 0
  have hdef := prefix_def _ _ (len p) hf hg
  have hm : ∀ k : M, k ≤ len p → F autoHistory ![k,z,0] = F autoHistory ![k,p,0] := by
    intro k
    induction k using ISigma1.sigma1_succ_induction with
    | hP => exact hdef
    | zero =>
      intro _
      change F (PA194ParamHistory.historyCode autoNext) ![0,z,0] = F (PA194ParamHistory.historyCode autoNext) ![0,p,0]
      rw [PA194ParamHistory.modelBase,PA194ParamHistory.modelBase]
    | succ k ih =>
      intro hlen
      have hk : k < len p := lt_iff_succ_le.mpr hlen
      have hz : k < len z := by rw [hj.1]; exact lt_of_lt_of_le hk le_self_add
      rw [autoHistory_step,autoHistory_step,if_pos hz,if_pos hk,hj.2.1 k hk,ih (le_of_lt hk)]
  exact hm n hn

theorem agree_def_generic (f g : M → M) (look : M → M → M) (bound : M)
    (hf : 𝚺₁-Function₁ f) (hg : 𝚺₁-Function₁ g) (hl : 𝚺₁-Function₂ look) :
    𝚺₁-Predicate (fun k => k ≤ bound → ∀ i < k, look i (f k) ≠ 0 → look i (g k) = look i (f k)) := by
  haveI := hf
  haveI := hg
  haveI := hl
  definability

theorem shifted_function_def (f : M → M) (a : M) (hf : 𝚺₁-Function₁ f) :
    𝚺₁-Function₁ (fun k => f (a+k)) := by
  haveI := hf
  definability

theorem joined_replay (p q z k : M) (hj : Joined p q z) (hk : k ≤ len q) :
    AgreeAccepted k (F autoHistory ![k,q,0]) (F autoHistory ![len p+k,z,0]) := by
  have hf : 𝚺₁-Function₁ (fun k : M => F autoHistory ![k,q,0]) :=
    PA194CodeInstance.unary_of_three autoHistory q 0
  have hg : 𝚺₁-Function₁ (fun k : M => F autoHistory ![len p+k,z,0]) :=
    shifted_function_def _ (len p) (PA194CodeInstance.unary_of_three autoHistory z 0)
  have hl : 𝚺₁-Function₂ (fun i h : M => F lookup ![i,h]) := by
    have h : 𝚺₁.DefinableFunction (fun e : Fin 2 → M => F lookup e) :=
      HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) lookup)
    convert h using 1
    funext e
    exact congrArg (fun e : Fin 2 → M => F lookup e) (Matrix.fun_eq_vec_two e).symm
  have hdef := agree_def_generic _ _ _ (len q) hf hg hl
  have hm : ∀ k : M, k ≤ len q → AgreeAccepted k (F autoHistory ![k,q,0]) (F autoHistory ![len p+k,z,0]) := by
    intro k
    induction k using ISigma1.sigma1_succ_induction with
    | hP => exact hdef
    | zero =>
      intro _ i hi
      exact False.elim (not_lt_zero hi)
    | succ k ih =>
      intro hbound i hi hnon
      have hklt : k < len q := lt_iff_succ_le.mpr hbound
      have hk : k ≤ len q := le_of_lt hklt
      rcases zero_or_succ i with rfl | ⟨j,rfl⟩
      · rw [autoHistory_newest,if_pos hklt] at hnon
        have hzk : len p+k < len z := by rw [hj.1]; exact (add_lt_add_iff_left (len p)).mpr hklt
        have hadd : len p+(k+1) = (len p+k)+1 := by ac_rfl
        rw [hadd,autoHistory_newest,if_pos hzk,hj.2.2 k hklt]
        rw [autoHistory_newest,if_pos hklt]
        rcases zero_or_succ (F extended ![k,F autoHistory ![k,q,0],q.[k]]) with hz | ⟨r,hr⟩
        · exact False.elim (hnon hz)
        · rw [hr]
          exact extended_replay k (len p+k) _ _ _ r (by simp) (ih hk) hr
      · have hjlt : j < k := (add_lt_add_iff_right 1).mp hi
        rw [autoHistory_earlier] at hnon
        have hadd : len p+(k+1) = (len p+k)+1 := by ac_rfl
        rw [hadd,autoHistory_earlier,autoHistory_earlier]
        exact ih hk j hjlt hnon
  exact hm k hk

theorem joined_first_result (p q z result : M) (hj : Joined p q z) (hp : TargetProof p result) :
    F lookup ![len q,F autoHistory ![len p+len q,z,0]] = result+1 := by
  obtain ⟨hpos,hroot⟩ := hp
  have hroot' : F lookup ![0,F autoHistory ![len p,p,0]] = result+1 := by
    simpa [rootCode_model] using hroot
  have hpref := joined_prefix p q z (len p) hj (le_refl _)
  have hz : len p ≠ 0 := ne_of_gt hpos
  obtain ⟨j,hj⟩ := (zero_or_succ (len p)).resolve_left hz
  have hr := PA194ParamHistory.modelHistoryReverse autoNext firstProjection secondProjection
    firstProjection_certified secondProjection_certified j (len q) z 0
  have h0 := PA194ParamHistory.modelHistoryReverse autoNext firstProjection secondProjection
    firstProjection_certified secondProjection_certified j 0 z 0
  change F lookup ![len q,F autoHistory ![j+len q+1,z,0]] = _ at hr
  change F lookup ![0,F autoHistory ![j+0+1,z,0]] = _ at h0
  have ht := hr.trans h0.symm
  have hstage : j+len q+1 = len p+len q := by rw [hj]; ac_rfl
  have hstage0 : j+0+1 = len p := by rw [hj]; simp
  rw [hstage,hstage0,hpref] at ht
  exact ht.trans hroot'

theorem joined_second_result (p q z result : M) (hj : Joined p q z) (hq : TargetProof q result) :
    F lookup ![0,F autoHistory ![len p+len q,z,0]] = result+1 := by
  obtain ⟨hpos,hroot⟩ := hq
  have hroot' : F lookup ![0,F autoHistory ![len q,q,0]] = result+1 := by
    simpa [rootCode_model] using hroot
  have hnon : F lookup ![0,F autoHistory ![len q,q,0]] ≠ 0 := by rw [hroot']; simp
  have ha := joined_replay p q z (len q) hj (le_refl _)
  have h := ha 0 hpos hnon
  rw [hroot'] at h
  exact h

theorem mp_closed (a b : M) : TargetProvable a → TargetProvable (impValue a b) → TargetProvable b := by
  rintro ⟨p,hp⟩ ⟨q,hq⟩
  obtain ⟨z,hz⟩ := joined_exists p q
  have hpv := joined_first_result p q z a hz hp
  have hqv := joined_second_result p q z (impValue a b) hz hq
  have hposp : 0 < len p := hp.1
  have hposz : 0 < len z := by rw [hz.1]; exact lt_of_lt_of_le hposp le_self_add
  have hoff : len q < len z := by
    rw [hz.1]
    have h := add_lt_add_right hposp (len q)
    simpa [add_comm] using h
  let line : M := pair 2 (pair b (pair (len q) 0))
  refine ⟨concat z line,?_⟩
  constructor
  · simp
  · rw [rootCode_model,len_concat,autoHistory_newest,len_concat,if_pos (lt_add_one (len z)),
      concat_nth_len,prefix_history z line (len z) (le_refl _)]
    rw [fallback (len z) _ 2 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),mp_step]
    rw [if_pos hoff,if_pos hposz,hz.1,hpv,hqv]
    exact (PA194TargetMP.check_correct (a+1) (impValue a b+1) b).mpr ⟨a,rfl,rfl⟩

theorem targetHistory_closed (program spare n i result : M) (hi : i < n)
    (h : F lookup ![i,F autoHistory ![n,program,spare]] = result+1) : TargetProvable result :=
  autoAccepted_sound TargetProvable targetProvable_definable head1_provable generalize_closed mp_closed
    target_leaf_closure program spare n i result hi h

#print axioms targetHistory_closed
#print axioms joined_first_result
#print axioms joined_second_result
#print axioms mp_closed
#print axioms joined_prefix
#print axioms joined_replay
#print axioms joined_exists
end models
end PA194TargetVectorJoin
