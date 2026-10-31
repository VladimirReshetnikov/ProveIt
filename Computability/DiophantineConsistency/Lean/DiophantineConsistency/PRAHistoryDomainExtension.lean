import DiophantineConsistency.PRAHistorySeqConsMembership
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistoryDomainExtension
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

theorem bit_lt {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    (hexp : ∀ i : V, ∃ p, Exponential i p) {i a : V}
    (h : bitDef.val.Evalb ![i,a]) : i < a := by
  obtain ⟨p,hp⟩ := hexp i
  have hl := (PRAHistoryInsertMembership.bit_iff_lenbit i a p hp).mp h
  exact lt_of_lt_of_le hp.lt hl.le

set_option maxHeartbeats 2000000 in
theorem domain_iff {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    (hexp : ∀ i : V, ∃ p, Exponential i p) (d s : V) :
    domainDef.val.Evalb ![d,s] ↔ ∀ i : V,
      (bitDef.val.Evalb ![i,d] ↔ ∃ y < s, memRel.val.Evalb ![s,i,y]) := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have rel (i y : V) : memRel.val.Evalb ![s,i,y] ↔ bitDef.val.Evalb ![pair i y,s] :=
    PRAHistorySeqConsMembership.memRel_iff s i y
  have dgraph : domainDef.val.Evalb ![d,s] ↔ ∀ i < d+s,
      (bitDef.val.Evalb ![i,d] ↔ ∃ y < s, ∃ z < s,
        bitDef.val.Evalb ![z,s] ∧ pairDef.val.Evalb ![z,i,y]) := by
    simp [domainDef, bexsIn, Semiformula.ballLT, Semiformula.bexsLT,
      FirstOrder.ball, FirstOrder.bexs, Semiformula.Operator.val, operator_mem_def,
      Semiformula.Operator.LT.sentence_eq, LogicalConnective.iff, iff_def]
  rw [dgraph]
  constructor
  · intro h i
    constructor
    · intro hi
      have hb : i < d+s := lt_of_lt_of_le (bit_lt hexp hi) (by simp)
      obtain ⟨y,hy,z,_,hz,hp⟩ := (h i hb).mp hi
      have heq : z = pair i y := (pair_defined.defined ![z,i,y]).mp hp
      exact ⟨y,hy,(rel i y).mpr (by simpa [heq] using hz)⟩
    · rintro ⟨y,hy,hr⟩
      have hp : bitDef.val.Evalb ![pair i y,s] := (rel i y).mp hr
      have hpair : pair i y < s := bit_lt hexp hp
      have hi : i < d+s := lt_of_lt_of_le (lt_of_le_of_lt (le_pair_left i y) hpair) (by simp)
      exact (h i hi).mpr ⟨y,hy,pair i y,hpair,hp,(pair_defined.defined ![pair i y,i,y]).mpr rfl⟩
  · intro h i hi
    constructor
    · intro hd
      obtain ⟨y,hy,hr⟩ := (h i).mp hd
      have hp := (rel i y).mp hr
      have hpair : pair i y < s := bit_lt hexp hp
      exact ⟨y,hy,pair i y,hpair,hp,(pair_defined.defined ![pair i y,i,y]).mpr rfl⟩
    · rintro ⟨y,hy,z,_,hz,hp⟩
      have heq : z = pair i y := (pair_defined.defined ![z,i,y]).mp hp
      apply (h i).mpr
      exact ⟨y,hy,(rel i y).mpr (by simpa [heq] using hz)⟩

theorem memRel_value_lt {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    (hexp : ∀ i : V, ∃ p, Exponential i p) {s i y : V}
    (h : memRel.val.Evalb ![s,i,y]) : y < s := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have hp := (PRAHistorySeqConsMembership.memRel_iff s i y).mp h
  exact lt_of_le_of_lt (le_pair_right i y) (bit_lt hexp hp)

set_option maxHeartbeats 2000000 in
theorem append_domain {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    (hexp : ∀ i : V, ∃ p, Exponential i p) (t s x : V)
    (ht : seqConsDef.val.Evalb ![t,s,x]) :
    ∃ l ≤ 2*s, lhDef.val.Evalb ![l,s] ∧ ∀ d d' : V,
      domainDef.val.Evalb ![d,s] → insertDef.val.Evalb ![d',l,d] →
        domainDef.val.Evalb ![d',t] := by
  obtain ⟨l,hl,hld,hm⟩ := PRAHistorySeqConsMembership.seqCons_membership hexp t s x ht
  refine ⟨l,hl,hld,?_⟩
  intro d d' hd hins
  have old := (domain_iff hexp d s).mp hd
  apply (domain_iff hexp d' t).mpr
  intro i
  obtain ⟨p,hp⟩ := hexp i
  obtain ⟨q,hq⟩ := hexp l
  have hbit := PRAHistoryInsertMembership.insert_membership d' i l d p q hp hq hins
  rw [hbit,old i]
  constructor
  · rintro (hi | ⟨y,hy,hr⟩)
    · have hn : memRel.val.Evalb ![t,i,x] := (hm i x).mpr (Or.inl ⟨hi,rfl⟩)
      exact ⟨x,memRel_value_lt hexp hn,hn⟩
    · have hn := (hm i y).mpr (Or.inr hr)
      exact ⟨y,memRel_value_lt hexp hn,hn⟩
  · rintro ⟨y,_,hy⟩
    rcases (hm i y).mp hy with ⟨hi,_⟩ | hr
    · exact Or.inl hi
    · exact Or.inr ⟨y,memRel_value_lt hexp hr,hr⟩

noncomputable def domainBody : ArithmeticSemisentence 2 :=
  “d s. !domainDef d s ↔ ∀ i, (i ∈ d ↔ ∃ y < s, !memRel s i y)”

theorem candidate_domain_iff : PRATheory.PRA ⊢ Semiformula.lMap PRALanguage.embedding
    (∀⁰* domainBody) := by
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
  have h := domain_iff hexp (e 0) (e 1)
  simpa [domainBody, Semiformula.bexsLT, FirstOrder.bexs, Semiformula.Operator.val,
    operator_mem_def, Semiformula.Operator.LT.sentence_eq, LogicalConnective.iff, iff_def] using h

noncomputable def appendDomainBody : ArithmeticSemisentence 3 :=
  “t s x. !seqConsDef t s x → ∃ l <⁺ 2*s, !lhDef l s ∧ ∀ d, ∀ d',
    !domainDef d s → !insertDef d' l d → !domainDef d' t”

theorem candidate_append_domain : PRATheory.PRA ⊢ Semiformula.lMap PRALanguage.embedding
    (∀⁰* appendDomainBody) := by
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
  have h := append_domain hexp (e 0) (e 1) (e 2)
  simpa [appendDomainBody, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
    Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le] using h
end DiophantineConsistency.PRAHistoryDomainExtension
