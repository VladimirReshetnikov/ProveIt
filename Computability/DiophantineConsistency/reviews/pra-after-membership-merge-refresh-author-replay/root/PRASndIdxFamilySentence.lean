import DiophantineConsistency.PRASndIdxFamilyBound
set_option autoImplicit false
namespace DiophantineConsistency.PRASndIdxFamilySentence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRASndIdxFamilyBound PRAWitnessFold StrictSigmaOneInduction

def familyBody : Semisentence language 3 :=
  Semiformula.rel Language.ORing.Rel.lt ![#1,#2] 🡒
    ((Rew.subst ![#0,#1] ▹ Semiformula.lMap embedding sndIdxDef.val) 🡒
      (Rew.subst ![#0,#1,applyCode (foldCode Code.succ) ![#2]] ▹
        Semiformula.lMap embedding (bnd sndIdxDef.val)))

def familySentence : Sentence language := ∀⁰* familyBody

theorem candidate_proves_sndIdx_family : PRA ⊢ familySentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  simp only [models_iff, familySentence, Semiformula.eval_allClosure]
  intro e
  simp only [familyBody, LogicalConnective.HomClass.map_imply, Semiformula.eval_rew]
  intro hp hx
  have hp' : Structure.rel (L := language) Language.ORing.Rel.lt ![e 1,e 2] := by
    have hv : (Semiterm.val e Empty.elim ∘ ![(#1 : TermN 3),#2]) = ![e 1,e 2] := by
      simpa only [Semiterm.val_bvar] using val_term_pair e (#1) (#2)
    change Structure.rel (L := language) Language.ORing.Rel.lt
      (Semiterm.val e Empty.elim ∘ ![(#1 : TermN 3),#2]) at hp
    simpa only [hv] using hp
  have hx' : (Semiformula.lMap embedding sndIdxDef.val).Eval ![e 0,e 1] Empty.elim := by
    have hv : (Semiterm.val e Empty.elim ∘ Rew.subst ![(#0 : TermN 3),#1] ∘ Semiterm.bvar) = ![e 0,e 1] := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      exact Fin.cases rfl (fun j => Fin.elim0 j) j
    have hf : (Semiterm.val e Empty.elim ∘ Rew.subst ![(#0 : TermN 3),#1] ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
    simpa only [hv, hf] using hx
  have hb := modelSndIdxFoldBound (e 2) (e 1) (e 0) hp' hx'
  have hv : (Semiterm.val e Empty.elim ∘
      Rew.subst ![#0,#1,applyCode (foldCode Code.succ) ![#2]] ∘ Semiterm.bvar) =
      ![e 0,e 1,Structure.func (L := language) (foldCode Code.succ) ![e 2]] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases ?_ (fun j => Fin.elim0 j) j
    simp [Function.comp_def, Rew.subst, applyCode, Semiterm.val_func]
    congr 1
    funext j
    exact Fin.cases rfl (fun j => Fin.elim0 j) j
  have hf : (Semiterm.val e Empty.elim ∘
      Rew.subst ![(#0 : TermN 3),#1,applyCode (foldCode Code.succ) ![#2]] ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  simpa only [hv, hf] using hb
end DiophantineConsistency.PRASndIdxFamilySentence
