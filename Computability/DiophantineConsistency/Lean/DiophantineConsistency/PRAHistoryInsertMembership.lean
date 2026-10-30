import DiophantineConsistency.PRAHistorySeqConsCode
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistoryInsertMembership
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

set_option maxHeartbeats 2000000 in
theorem bit_iff_lenbit {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    (i s p : V) (hp : Exponential i p) : bitDef.val.Evalb ![i,s] ↔ LenBit p s := by
  have hexp : ∀ e : V, expDef.val.Evalb ![e,i] ↔ Exponential i e := by
    intro e
    simp [expDef, Semiformula.eval_substs]
  have hlen : ∀ e : V, lenbitDef.val.Evalb ![e,s] ↔ LenBit e s := by
    intro e
    exact lenbit_defined.defined ![e,s]
  have hb : bitDef.val.Evalb ![i,s] ↔ ∃ e ≤ s, expDef.val.Evalb ![e,i] ∧ lenbitDef.val.Evalb ![e,s] := by
    simp [bitDef, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
      Semiformula.Operator.val, Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le]
  rw [hb]
  simp only [hexp, hlen]
  constructor
  · rintro ⟨e,_,he,hl⟩
    rw [he.uniq hp] at hl
    exact hl
  · intro h
    exact ⟨p,h.le,hp,h⟩
set_option maxHeartbeats 2000000 in
theorem insert_membership {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    (t i j s p q : V) (hp : Exponential i p) (hq : Exponential j q)
    (ht : insertDef.val.Evalb ![t,j,s]) :
    bitDef.val.Evalb ![i,t] ↔ i = j ∨ bitDef.val.Evalb ![i,s] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have hexp (e : V) : expDef.val.Evalb ![e,j] ↔ Exponential j e := by
    simp [expDef, Semiformula.eval_substs]
  have hi := bit_iff_lenbit i s p hp
  have hj := bit_iff_lenbit j s q hq
  have hit := bit_iff_lenbit i t p hp
  have hij : p = q ↔ i = j := by
    constructor
    · intro h
      exact hp.inj (h ▸ hq)
    · intro h
      subst j
      exact hp.uniq hq
  rcases (PRAHistoryInsertCode.insert_iff t j s).mp ht with ⟨hmem,rfl⟩ | ⟨hmem,e,_,he,rfl⟩
  · constructor
    · intro h
      exact Or.inr h
    · rintro (rfl | h)
      · exact hmem
      · exact h
  · have heq := (hexp e).mp he |>.uniq hq
    subst e
    rw [hit,hi]
    rw [lenbit_add_pow2_iff_of_not_lenbit hp.range_pow2 hq.range_pow2 (fun h => hmem (hj.mpr h))]
    rw [hij]

noncomputable def insertMembershipBody : ArithmeticSemisentence 4 :=
  “t i j s. !insertDef t j s → (i ∈ t ↔ (i = j ∨ i ∈ s))”

theorem candidate_insert_membership : PRATheory.PRA ⊢ Semiformula.lMap PRALanguage.embedding (∀⁰* insertMembershipBody) := by
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
  have hmodel (t i j s : M) : insertDef.val.Evalb ![t,j,s] →
      (bitDef.val.Evalb ![i,t] ↔ i = j ∨ bitDef.val.Evalb ![i,s]) := by
    intro h
    let p := Structure.func (L := PRALanguage.language) PRAHistoryExpCode.expCode (fun _ => i)
    let q := Structure.func (L := PRALanguage.language) PRAHistoryExpCode.expCode (fun _ => j)
    have hp := (PRAHistoryExpCode.graph_iff i p).mp (PRAHistoryExpCode.modelExpCode i)
    have hq := (PRAHistoryExpCode.graph_iff j q).mp (PRAHistoryExpCode.modelExpCode j)
    exact insert_membership t i j s p q hp hq h
  rw [Semiformula.models_lMap, PRAModelIOpenPairing.reduct_eq_standard]
  simp only [models_iff, Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_four e]
  simpa [insertMembershipBody, Semiformula.Operator.val, operator_mem_def,
    Semiformula.Operator.Eq.sentence_eq, LogicalConnective.iff, iff_def] using hmodel (e 0) (e 1) (e 2) (e 3)
end DiophantineConsistency.PRAHistoryInsertMembership
