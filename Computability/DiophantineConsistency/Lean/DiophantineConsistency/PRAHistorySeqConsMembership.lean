import DiophantineConsistency.PRAHistoryInsertMembership
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistorySeqConsMembership
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

set_option maxHeartbeats 2000000 in
theorem memRel_iff {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (r i z : V) :
    memRel.val.Evalb ![r,i,z] ↔ bitDef.val.Evalb ![pair i z,r] := by
  have h : memRel.val.Evalb ![r,i,z] ↔ ∃ p ≤ (i+z+1)^2,
      pairDef.val.Evalb ![p,i,z] ∧ bitDef.val.Evalb ![p,r] := by
    simp [memRel, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
      Semiformula.Operator.val, operator_mem_def, Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le]
  rw [h]
  constructor
  · rintro ⟨p,_,hp,hb⟩
    have he : p = pair i z := (pair_defined.defined ![p,i,z]).mp hp
    simpa [he] using hb
  · intro hb
    refine ⟨pair i z,pair_polybound i z,?_,hb⟩
    exact (pair_defined.defined ![pair i z,i,z]).mpr rfl
set_option maxHeartbeats 2000000 in
theorem seqCons_membership {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    (hexp : ∀ i : V, ∃ p, Exponential i p) (t s x : V)
    (ht : seqConsDef.val.Evalb ![t,s,x]) :
    ∃ l ≤ 2*s, lhDef.val.Evalb ![l,s] ∧ ∀ i z : V,
      (memRel.val.Evalb ![t,i,z] ↔ (i = l ∧ z = x) ∨ memRel.val.Evalb ![s,i,z]) := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  obtain ⟨l,hl,hld,p,_,hp,hins⟩ := (PRAHistorySeqConsCode.seqCons_iff t s x).mp ht
  have peq : p = pair l x := (pair_defined.defined ![p,l,x]).mp hp
  subst p
  refine ⟨l,hl,hld,?_⟩
  intro i z
  obtain ⟨pi,hpi⟩ := hexp (pair i z)
  obtain ⟨pj,hpj⟩ := hexp (pair l x)
  rw [memRel_iff,memRel_iff]
  have h := PRAHistoryInsertMembership.insert_membership t (pair i z) (pair l x) s pi pj hpi hpj hins
  rw [h]
  simp only [pair_ext_iff]

noncomputable def seqConsMembershipBody : ArithmeticSemisentence 3 :=
  “t s x. !seqConsDef t s x → ∃ l <⁺ 2*s, !lhDef l s ∧ ∀ i, ∀ z,
    (!memRel t i z ↔ ((i = l ∧ z = x) ∨ !memRel s i z))”

theorem candidate_seqCons_membership : PRATheory.PRA ⊢ Semiformula.lMap PRALanguage.embedding
    (∀⁰* seqConsMembershipBody) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  letI : Zero M := ⟨Structure.func (L := PRALanguage.language) (PRAFiniteFunctionCodes.Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := PRALanguage.language) PRALanguage.oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := PRALanguage.language) PRALanguage.addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := PRALanguage.language) PRALanguage.mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  have hexp (i : M) : ∃ p, Exponential i p := by
    let p := Structure.func (L := PRALanguage.language) PRAHistoryExpCode.expCode (fun _ => i)
    exact ⟨p,(PRAHistoryExpCode.graph_iff i p).mp (PRAHistoryExpCode.modelExpCode i)⟩
  rw [Semiformula.models_lMap, PRAModelIOpenPairing.reduct_eq_standard]
  simp only [models_iff, Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_three e]
  have h := seqCons_membership hexp (e 0) (e 1) (e 2)
  simpa [seqConsMembershipBody, Semiformula.bexsLTSucc, Semiformula.bexsLT,
    FirstOrder.bexs, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le, LogicalConnective.iff, iff_def] using h
end DiophantineConsistency.PRAHistorySeqConsMembership
