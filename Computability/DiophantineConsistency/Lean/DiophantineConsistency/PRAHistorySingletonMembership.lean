import DiophantineConsistency.PRAHistorySeqConsMembership
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistorySingletonMembership
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

set_option maxHeartbeats 2000000 in
theorem seq_zero {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] :
    seqDef.val.Evalb ![(0 : V)] ∧ lhDef.val.Evalb ![(0 : V),0] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have hd : domainDef.val.Evalb ![(0 : V),0] := by
    simp [domainDef, Semiformula.ballLT, FirstOrder.ball]
  have hu : underDef.val.Evalb ![(0 : V),0] := by
    simp [underDef, expDef, Semiformula.eval_substs]
  have hm : isMappingDef.val.Evalb ![(0 : V)] := by
    simp [isMappingDef, Semiformula.bexsLTSucc, Semiformula.bexsLT,
      FirstOrder.bexs, Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq,
      ballIn, Semiformula.ballLT, FirstOrder.ball, hd]
  have hs : seqDef.val.Evalb ![(0 : V)] := by
    simp [seqDef, Semiformula.bexsLTSucc, Semiformula.bexsLT,
      FirstOrder.bexs, Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq,
      hm, hd, hu]
  refine ⟨hs,?_⟩
  simp [lhDef, Semiformula.bexsLTSucc, Semiformula.bexsLT,
    FirstOrder.bexs, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq, hs, hd, hu]

set_option maxHeartbeats 2000000 in
theorem lh_zero_unique {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    (l : V) (hl : lhDef.val.Evalb ![l,0]) : l = 0 := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have hs := (seq_zero (V := V)).1
  simp [lhDef, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
    Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq, hs] at hl
  have h : Exponential l (1 : V) := by
    simpa [underDef, expDef, Semiformula.eval_substs] using hl.2
  exact h.inj (by simp : Exponential (0 : V) 1)

set_option maxHeartbeats 2000000 in
theorem empty_memRel {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    (hexp : ∀ i : V, ∃ p, Exponential i p) (i z : V) :
    ¬memRel.val.Evalb ![(0 : V),i,z] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  rw [PRAHistorySeqConsMembership.memRel_iff]
  obtain ⟨p,hp⟩ := hexp (pair i z)
  intro h
  have hl := (PRAHistoryInsertMembership.bit_iff_lenbit (pair i z) 0 p hp).mp h
  exact not_lt_of_ge hl.le hp.range_pos

set_option maxHeartbeats 2000000 in
theorem singleton_memRel {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    (hexp : ∀ i : V, ∃ p, Exponential i p) (t x : V)
    (ht : seqConsDef.val.Evalb ![t,0,x]) (i z : V) :
    memRel.val.Evalb ![t,i,z] ↔ i = 0 ∧ z = x := by
  obtain ⟨l,_,hl,hm⟩ := PRAHistorySeqConsMembership.seqCons_membership hexp t 0 x ht
  have hzero := lh_zero_unique l hl
  rw [hm i z,hzero]
  simp [empty_memRel hexp i z]

noncomputable def singletonBody : ArithmeticSemisentence 2 :=
  “t x. !seqConsDef t 0 x → ∀ i, ∀ z, (!memRel t i z ↔ (i = 0 ∧ z = x))”

theorem candidate_singleton_memRel : PRATheory.PRA ⊢ Semiformula.lMap PRALanguage.embedding
    (∀⁰* singletonBody) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  letI : Zero M := ⟨Structure.func (L := PRALanguage.language) (PRAFiniteFunctionCodes.Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := PRALanguage.language) PRALanguage.oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := PRALanguage.language) PRALanguage.addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := PRALanguage.language) PRALanguage.mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
    have h := PRAModelISigmaZero.modelReductISigmaZero (M := M)
    rw [PRAModelIOpenPairing.reduct_eq_standard] at h
    exact h
  have hexp (i : M) : ∃ p, Exponential i p := by
    let p := Structure.func (L := PRALanguage.language) PRAHistoryExpCode.expCode (fun _ => i)
    exact ⟨p,(PRAHistoryExpCode.graph_iff i p).mp (PRAHistoryExpCode.modelExpCode i)⟩
  rw [Semiformula.models_lMap, PRAModelIOpenPairing.reduct_eq_standard]
  simp only [models_iff, Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_two e]
  have h := singleton_memRel hexp (e 0) (e 1)
  simpa [singletonBody, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    LogicalConnective.iff, iff_def] using h
end DiophantineConsistency.PRAHistorySingletonMembership
