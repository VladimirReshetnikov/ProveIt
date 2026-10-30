import DiophantineConsistency.PRAHistoryDomainExtension
import DiophantineConsistency.PRAHistoryUnderExtension
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistorySequenceExtension
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

set_option maxHeartbeats 2000000 in
theorem mapping_iff {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    (hexp : ∀ i : V, ∃ p, Exponential i p) (s : V) :
    isMappingDef.val.Evalb ![s] ↔ ∃ d ≤ 2*s, domainDef.val.Evalb ![d,s] ∧
      ∀ i : V, bitDef.val.Evalb ![i,d] → ∃ y < s, memRel.val.Evalb ![s,i,y] ∧
        ∀ y' < s, memRel.val.Evalb ![s,i,y'] → y' = y := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  simp [isMappingDef, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
    ballIn, Semiformula.ballLT, FirstOrder.ball, Semiformula.Operator.val,
    Semiformula.Operator.LT.sentence_eq, Semiformula.Operator.Eq.sentence_eq,
    operator_mem_def, lt_succ_iff_le]
  constructor
  · rintro ⟨d,hd,hdom,h⟩
    refine ⟨d,hd,hdom,?_⟩
    intro i hi
    exact h i (PRAHistoryDomainExtension.bit_lt hexp hi) hi
  · rintro ⟨d,hd,hdom,h⟩
    refine ⟨d,hd,hdom,?_⟩
    intro i _ hi
    exact h i hi

theorem domain_insert_of_append {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    (hexp : ∀ i : V, ∃ p, Exponential i p) (t s x l d d' : V)
    (hm : ∀ i z : V, memRel.val.Evalb ![t,i,z] ↔
      (i = l ∧ z = x) ∨ memRel.val.Evalb ![s,i,z])
    (hd : domainDef.val.Evalb ![d,s]) (hins : insertDef.val.Evalb ![d',l,d]) :
    domainDef.val.Evalb ![d',t] := by
  have old := (PRAHistoryDomainExtension.domain_iff hexp d s).mp hd
  apply (PRAHistoryDomainExtension.domain_iff hexp d' t).mpr
  intro i
  obtain ⟨p,hp⟩ := hexp i
  obtain ⟨q,hq⟩ := hexp l
  have hbit := PRAHistoryInsertMembership.insert_membership d' i l d p q hp hq hins
  rw [hbit,old i]
  constructor
  · rintro (hi | ⟨y,_,hr⟩)
    · have hn : memRel.val.Evalb ![t,i,x] := (hm i x).mpr (Or.inl ⟨hi,rfl⟩)
      exact ⟨x,PRAHistoryDomainExtension.memRel_value_lt hexp hn,hn⟩
    · have hn := (hm i y).mpr (Or.inr hr)
      exact ⟨y,PRAHistoryDomainExtension.memRel_value_lt hexp hn,hn⟩
  · rintro ⟨y,_,hy⟩
    rcases (hm i y).mp hy with ⟨hi,_⟩ | hr
    · exact Or.inl hi
    · exact Or.inr ⟨y,PRAHistoryDomainExtension.memRel_value_lt hexp hr,hr⟩

set_option maxHeartbeats 4000000 in
theorem append_sequence {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    (hexp : ∀ i : V, ∃ p, Exponential i p) (t s x : V)
    (hs : seqDef.val.Evalb ![s]) (ht : seqConsDef.val.Evalb ![t,s,x]) :
    seqDef.val.Evalb ![t] ∧ ∃ l ≤ 2*s, lhDef.val.Evalb ![l,s] ∧
      lhDef.val.Evalb ![l+1,t] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  obtain ⟨l,hl,hld,hm⟩ := PRAHistorySeqConsMembership.seqCons_membership hexp t s x ht
  have hld' := hld
  simp [lhDef, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
    Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le, hs] at hld'
  obtain ⟨d,hd,hdom,hu⟩ := hld'
  have hmap : isMappingDef.val.Evalb ![s] := by
    have h := hs
    simp [seqDef, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
      Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le] at h
    exact h.1
  obtain ⟨d₀,_,hdom₀,hmap₀⟩ := (mapping_iff hexp s).mp hmap
  have hdomEq (i : V) : bitDef.val.Evalb ![i,d] ↔ bitDef.val.Evalb ![i,d₀] :=
    ((PRAHistoryDomainExtension.domain_iff hexp d s).mp hdom i).trans
      (((PRAHistoryDomainExtension.domain_iff hexp d₀ s).mp hdom₀ i).symm)
  have hp := (PRAHistoryUnderExtension.under_iff_exponential d l).mp hu
  have hno : ¬bitDef.val.Evalb ![l,d] := by
    rw [PRAHistoryInsertMembership.bit_iff_lenbit l d (d+1) hp]
    exact not_lenbit_of_lt (by simp)
  let d' := d+(d+1)
  have hins : insertDef.val.Evalb ![d',l,d] := by
    apply (PRAHistoryInsertCode.insert_iff d' l d).mpr
    right
    have he : expDef.val.Evalb ![d+1,l] := by
      simpa [expDef, Semiformula.eval_substs] using hp
    exact ⟨hno,d+1,by simp [d'],he,rfl⟩
  have hdom' := domain_insert_of_append hexp t s x l d d' hm hdom hins
  have hu' := PRAHistoryUnderExtension.append_under d d' l hu hins
  have hnew : memRel.val.Evalb ![t,l,x] := (hm l x).mpr (Or.inl ⟨rfl,rfl⟩)
  have hnewBit := (PRAHistorySeqConsMembership.memRel_iff t l x).mp hnew
  obtain ⟨q,hq⟩ := hexp (pair l x)
  have hqle : q ≤ t := ((PRAHistoryInsertMembership.bit_iff_lenbit (pair l x) t q hq).mp hnewBit).le
  have hpowle : d+1 ≤ q := hp.monotone_le hq (le_pair_left l x)
  have hdt : d+1 ≤ t := le_trans hpowle hqle
  have hd' : d' ≤ 2*t := by
    dsimp [d']
    calc
      d+(d+1) ≤ (d+1)+(d+1) := add_le_add (by simp) (le_refl _)
      _ ≤ t+t := add_le_add hdt hdt
      _ = 2*t := by simp [two_mul]
  have hlt : l+1 ≤ 2*t := by
    have hle : l ≤ d := lt_succ_iff_le.mp hp.lt
    have hplus : l+1 ≤ d+1 := by simpa [add_comm] using add_le_add_right hle 1
    have : l+1 ≤ t := le_trans hplus hdt
    exact le_trans this (by simp [two_mul])
  have hmap' : isMappingDef.val.Evalb ![t] := by
    apply (mapping_iff hexp t).mpr
    refine ⟨d',hd',hdom',?_⟩
    intro i hi
    obtain ⟨pi,hpi⟩ := hexp i
    have hbit := PRAHistoryInsertMembership.insert_membership d' i l d pi (d+1) hpi hp hins
    rcases hbit.mp hi with hil | hold
    · have hnone : ¬∃ y, memRel.val.Evalb ![s,l,y] := by
        rintro ⟨y,hy⟩
        have hyl : y < s := PRAHistoryDomainExtension.memRel_value_lt hexp hy
        exact hno (((PRAHistoryDomainExtension.domain_iff hexp d s).mp hdom l).mpr ⟨y,hyl,hy⟩)
      have hy : x < t := PRAHistoryDomainExtension.memRel_value_lt hexp hnew
      refine ⟨x,hy,(hm i x).mpr (Or.inl ⟨hil,rfl⟩),?_⟩
      intro y _ hty
      rcases (hm i y).mp hty with ⟨_,heq⟩ | hold'
      · exact heq
      · exact False.elim (hnone ⟨y,by simpa [hil] using hold'⟩)
    · have h0 := hmap₀ i ((hdomEq i).mp hold)
      obtain ⟨y,hy,hyrel,huniq⟩ := h0
      have hynew := (hm i y).mpr (Or.inr hyrel)
      refine ⟨y,PRAHistoryDomainExtension.memRel_value_lt hexp hynew,hynew,?_⟩
      intro y' _ hy'rel
      rcases (hm i y').mp hy'rel with ⟨hil,_⟩ | hold'
      · have : bitDef.val.Evalb ![l,d] := by simpa [hil] using hold
        exact False.elim (hno this)
      · exact huniq y' (PRAHistoryDomainExtension.memRel_value_lt hexp hold') hold'
  have hs' : seqDef.val.Evalb ![t] := by
    simp [seqDef, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
      Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le]
    exact ⟨hmap',l+1,hlt,d',hd',hdom',hu'⟩
  refine ⟨hs',l,hl,hld,?_⟩
  simp [lhDef, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
    Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
    Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le, hs']
  exact ⟨d',hd',hdom',hu'⟩

noncomputable def appendSequenceBody : ArithmeticSemisentence 3 :=
  “t s x. !seqDef s → !seqConsDef t s x → !seqDef t ∧
    ∃ l <⁺ 2*s, !lhDef l s ∧ !lhDef (l+1) t”

theorem candidate_append_sequence : PRATheory.PRA ⊢ Semiformula.lMap PRALanguage.embedding
    (∀⁰* appendSequenceBody) := by
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
  rw [Matrix.fun_eq_vec_three e]
  have h := append_sequence hexp (e 0) (e 1) (e 2)
  simpa [appendSequenceBody, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
    Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le] using h
end DiophantineConsistency.PRAHistorySequenceExtension
