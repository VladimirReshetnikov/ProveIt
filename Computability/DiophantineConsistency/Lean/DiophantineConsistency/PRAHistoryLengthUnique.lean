import DiophantineConsistency.PRAHistoryUnderCanonical
import DiophantineConsistency.PRAHistoryDomainExtension
import DiophantineConsistency.PRAHistorySequenceExtension
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistoryLengthUnique
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

set_option maxHeartbeats 3000000 in
theorem modelLengthUnique (s a b : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
    lhDef.val.Evalb ![a,s] → lhDef.val.Evalb ![b,s] → a = b := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have hexp (i : M) : ∃ p, Exponential i p := by
    let p := Structure.func (L := language) PRAHistoryExpCode.expCode (fun _ => i)
    exact ⟨p,(PRAHistoryExpCode.graph_iff i p).mp (PRAHistoryExpCode.modelExpCode i)⟩
  intro ha hb
  by_cases hs : seqDef.val.Evalb ![s]
  · have ha' := ha
    have hb' := hb
    simp [lhDef, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
      Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
      Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le, hs] at ha' hb'
    obtain ⟨da,_,hda,hua⟩ := ha'
    obtain ⟨db,_,hdb,hub⟩ := hb'
    have hsame (i : M) : bitDef.val.Evalb ![i,da] ↔ bitDef.val.Evalb ![i,db] :=
      ((PRAHistoryDomainExtension.domain_iff hexp da s).mp hda i).trans
        (((PRAHistoryDomainExtension.domain_iff hexp db s).mp hdb i).symm)
    have haBits (i : M) := PRAHistoryUnderCanonical.modelUnderBits da a i hua
    have hbBits (i : M) := PRAHistoryUnderCanonical.modelUnderBits db b i hub
    have hlt (i : M) : i < a ↔ i < b := (haBits i).symm.trans ((hsame i).trans (hbBits i))
    have hab : a ≤ b := le_of_not_gt (fun h => (not_lt_of_ge (le_refl b)) ((hlt b).mp h))
    have hba : b ≤ a := le_of_not_gt (fun h => (not_lt_of_ge (le_refl a)) ((hlt a).mpr h))
    exact le_antisymm hab hba
  · simp [lhDef, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs,
      Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq,
      Semiformula.Operator.LT.sentence_eq, lt_succ_iff_le, hs] at ha hb
    rw [ha,hb]
theorem modelAppendLength (t s x l : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
    seqDef.val.Evalb ![s] → lhDef.val.Evalb ![l,s] → seqConsDef.val.Evalb ![t,s,x] →
      seqDef.val.Evalb ![t] ∧ lhDef.val.Evalb ![l+1,t] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  have hexp (i : M) : ∃ p, Exponential i p := by
    let p := Structure.func (L := language) PRAHistoryExpCode.expCode (fun _ => i)
    exact ⟨p,(PRAHistoryExpCode.graph_iff i p).mp (PRAHistoryExpCode.modelExpCode i)⟩
  intro hs hl ht
  obtain ⟨hseq,l',_,hl',hnext⟩ := PRAHistorySequenceExtension.append_sequence hexp t s x hs ht
  have heq : l' = l := modelLengthUnique s l' l hl' hl
  rw [heq] at hnext
  exact ⟨hseq,hnext⟩
end models

noncomputable def lengthUniqueBody : ArithmeticSemisentence 3 :=
  “s a b. !lhDef a s → !lhDef b s → a = b”

theorem candidate_length_unique : PRA ⊢ Semiformula.lMap embedding (∀⁰* lengthUniqueBody) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  rw [Semiformula.models_lMap,PRAModelIOpenPairing.reduct_eq_standard]
  simp only [models_iff,Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_three e]
  simpa [lengthUniqueBody, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq] using
    (modelLengthUnique (e 0) (e 1) (e 2))

noncomputable def appendLengthBody : ArithmeticSemisentence 4 :=
  “t s x l. !seqDef s → !lhDef l s → !seqConsDef t s x → !seqDef t ∧ !lhDef (l+1) t”

theorem candidate_append_length : PRA ⊢ Semiformula.lMap embedding (∀⁰* appendLengthBody) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  rw [Semiformula.models_lMap,PRAModelIOpenPairing.reduct_eq_standard]
  simp only [models_iff,Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_four e]
  simpa [appendLengthBody] using modelAppendLength (e 0) (e 1) (e 2) (e 3)
end DiophantineConsistency.PRAHistoryLengthUnique
