import DiophantineConsistency.PRAHistoryInsertMembership
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistoryUnderExtension
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

theorem under_iff_exponential {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] (d l : V) :
    underDef.val.Evalb ![d,l] ↔ Exponential l (d+1) := by
  simp [underDef, expDef, Semiformula.eval_substs]

theorem under_injective {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] (d a b : V)
    (ha : underDef.val.Evalb ![d,a]) (hb : underDef.val.Evalb ![d,b]) : a = b :=
  ((under_iff_exponential d a).mp ha).inj ((under_iff_exponential d b).mp hb)

set_option maxHeartbeats 2000000 in
theorem append_under {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    (d d' l : V) (hu : underDef.val.Evalb ![d,l]) (hi : insertDef.val.Evalb ![d',l,d]) :
    underDef.val.Evalb ![d',l+1] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have hp : Exponential l (d+1) := (under_iff_exponential d l).mp hu
  have hn : ¬bitDef.val.Evalb ![l,d] := by
    rw [PRAHistoryInsertMembership.bit_iff_lenbit l d (d+1) hp]
    exact not_lenbit_of_lt (by simp)
  rcases (PRAHistoryInsertCode.insert_iff d' l d).mp hi with ⟨hm,_⟩ | ⟨_,e,_,he,heq⟩
  · exact False.elim (hn hm)
  · have he' : Exponential l e := by simpa [expDef, Semiformula.eval_substs] using he
    have heq' : e = d+1 := he'.uniq hp
    rw [heq'] at heq
    rw [heq,under_iff_exponential]
    have hs := hp.succ
    have ha : d+(d+1)+1 = 2*(d+1) := by simp [two_mul, add_comm, add_left_comm]
    rw [ha]
    exact hs

noncomputable def appendUnderBody : ArithmeticSemisentence 3 :=
  “d d' l. !underDef d l → !insertDef d' l d → !underDef d' (l+1)”

theorem candidate_append_under : PRATheory.PRA ⊢ Semiformula.lMap PRALanguage.embedding
    (∀⁰* appendUnderBody) := by
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
  rw [Semiformula.models_lMap, PRAModelIOpenPairing.reduct_eq_standard]
  simp only [models_iff, Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_three e]
  simpa [appendUnderBody] using append_under (e 0) (e 1) (e 2)
end DiophantineConsistency.PRAHistoryUnderExtension
