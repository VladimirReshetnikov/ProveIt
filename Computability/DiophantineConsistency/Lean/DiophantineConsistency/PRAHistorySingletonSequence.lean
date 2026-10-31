import DiophantineConsistency.PRAHistoryDomainExtension
import DiophantineConsistency.PRAHistorySingletonMembership
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistorySingletonSequence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

theorem bit_one {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    (hexp : ∀ i : V, ∃ p, Exponential i p) (i : V) :
    bitDef.val.Evalb ![i,(1 : V)] ↔ i = 0 := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  obtain ⟨p,hp⟩ := hexp i
  rw [PRAHistoryInsertMembership.bit_iff_lenbit i 1 p hp]
  by_cases h : i = 0
  · subst i
    have hp1 : p = 1 := hp.zero_uniq
    subst p
    have hn : ¬(2 : V) ∣ 1 := not_dvd_of_lt (by simp) one_lt_two
    simp [LenBit,hn]
  · have hi : 1 ≤ i := pos_iff_one_le.mp (pos_iff_ne_zero.mpr h)
    have hp1 : 1 < p := lt_of_le_of_lt hi hp.lt
    simp [h,not_lenbit_of_lt hp1]

theorem singleton_domain {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    (hexp : ∀ i : V, ∃ p, Exponential i p) (t x : V)
    (ht : seqConsDef.val.Evalb ![t,0,x]) : domainDef.val.Evalb ![1,t] := by
  have hmem (i z : V) := PRAHistorySingletonMembership.singleton_memRel hexp t x ht i z
  have hx : memRel.val.Evalb ![t,0,x] := (hmem 0 x).mpr ⟨rfl,rfl⟩
  have hxt : x < t := PRAHistoryDomainExtension.memRel_value_lt hexp hx
  apply (PRAHistoryDomainExtension.domain_iff hexp 1 t).mpr
  intro i
  rw [bit_one hexp i]
  constructor
  · intro hi
    exact ⟨x,hxt,(hmem i x).mpr ⟨hi,rfl⟩⟩
  · rintro ⟨y,_,hy⟩
    exact ((hmem i y).mp hy).1

set_option maxHeartbeats 2000000 in
theorem singleton_sequence {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    (hexp : ∀ i : V, ∃ p, Exponential i p) (t x : V)
    (ht : seqConsDef.val.Evalb ![t,0,x]) :
    seqDef.val.Evalb ![t] ∧ lhDef.val.Evalb ![(1 : V),t] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have hmem (i z : V) := PRAHistorySingletonMembership.singleton_memRel hexp t x ht i z
  have hx : memRel.val.Evalb ![t,0,x] := (hmem 0 x).mpr ⟨rfl,rfl⟩
  have hxt : x < t := PRAHistoryDomainExtension.memRel_value_lt hexp hx
  have htpos : 0 < t := lt_of_le_of_lt (by simp) hxt
  have hone : (1 : V) ≤ 2*t := by
    calc
      1 ≤ t := pos_iff_one_le.mp htpos
      _ ≤ 2*t := by simp [two_mul]
  have hdom := singleton_domain hexp t x ht
  have hunder : underDef.val.Evalb ![(1 : V),1] := by
    have h1 : Exponential (1 : V) (1+1) := by
      have h := Exponential.succ (by simp : Exponential (0 : V) 1)
      simpa only [zero_add, two_mul] using h
    simpa [underDef, expDef, Semiformula.eval_substs] using h1
  have hm : isMappingDef.val.Evalb ![t] := by
    simp [isMappingDef, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
      ballIn, Semiformula.ballLT, FirstOrder.ball, Semiformula.Operator.val,
      Semiformula.Operator.LT.sentence_eq, Semiformula.Operator.Eq.sentence_eq,
      operator_mem_def, lt_succ_iff_le]
    refine ⟨1,hone,hdom,?_⟩
    intro i hi hbi
    have hi0 := (bit_one hexp i).mp hbi
    refine ⟨x,hxt,?_,?_⟩
    · exact (hmem i x).mpr ⟨hi0,rfl⟩
    · intro y hy hrel
      exact ((hmem i y).mp hrel).2
  have hs : seqDef.val.Evalb ![t] := by
    simp [seqDef, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
      Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le]
    exact ⟨hm,1,hone,1,hone,hdom,hunder⟩
  refine ⟨hs,?_⟩
  simp [lhDef, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
    Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le, hs]
  exact ⟨1,hone,hdom,hunder⟩

noncomputable def singletonSequenceBody : ArithmeticSemisentence 2 :=
  “t x. !seqConsDef t 0 x → !seqDef t ∧ !lhDef 1 t”

theorem candidate_singleton_sequence : PRATheory.PRA ⊢ Semiformula.lMap PRALanguage.embedding
    (∀⁰* singletonSequenceBody) := by
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
  rw [Matrix.fun_eq_vec_two e]
  simpa [singletonSequenceBody] using singleton_sequence hexp (e 0) (e 1)
end DiophantineConsistency.PRAHistorySingletonSequence
