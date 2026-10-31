import DiophantineConsistency.PRAHistorySetTermCode
import DiophantineConsistency.PRAHistoryResultGraph
set_option autoImplicit false
namespace DiophantineConsistency.PRAHistorySetTermResult
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
  PRAHistoryIterator PRAHistoryResultGraph

noncomputable def termBlueprint : PR.Blueprint 0 := (FormalizedTerm.blueprint ℒₛₑₜ).prBlueprint
def zeroCode : Code 0 := .zero 0
def swapStep (c : Code 2) : Code 2 := .comp c (.cons (.proj 1) (.cons (.proj 0) (.nil 2)))

theorem PRA_proves_termZero : PRA ⊢ zeroGraphSentence termBlueprint zeroCode := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  simp only [models_iff,zeroGraphSentence,Semiformula.eval_rew]
  have hv : (Semiterm.val (L := language) ![] (Empty.elim : Empty → M) ∘ zeroGraphRew zeroCode ∘ Semiterm.bvar) =
      ![Structure.func (L := language) (M := M) zeroCode Fin.elim0] := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    change Structure.func (L := language) zeroCode
      (Semiterm.val (L := language) ![] (Empty.elim : Empty → M) ∘ Fin.elim0) = _
    congr 1
    exact Subsingleton.elim _ _
  have he : (Semiterm.val (L := language) ![] (Empty.elim : Empty → M) ∘ zeroGraphRew zeroCode ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he,Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard]
  simp [termBlueprint, Fixpoint.Blueprint.prBlueprint, zeroCode]
  rfl

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Structure.Eq language M] in
theorem modelTermSucc (c : Code 2)
    (hc : PRA ⊢ PRAHistoryFixpointSuccCode.graphSentence (FormalizedTerm.blueprint ℒₛₑₜ) c)
    (ih s : M) :
    (Semiformula.lMap embedding (FormalizedTerm.blueprint ℒₛₑₜ).succDef.val).Eval
      ![Structure.func (L := language) c ![ih,s],ih,s] Empty.elim := by
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hc
  simp only [models_iff,PRAHistoryFixpointSuccCode.graphSentence,Semiformula.eval_allClosure] at hm
  have hm := hm ![ih,s]
  simp only [Semiformula.eval_rew] at hm
  have hv : (Semiterm.val (L := language) ![ih,s] Empty.elim ∘
      PRAHistoryFixpointSuccCode.graphRew c ∘ Semiterm.bvar) =
      ![Structure.func (L := language) c ![ih,s],ih,s] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) c
        (Semiterm.val (L := language) ![ih,s] Empty.elim ∘ ![#0,#1]) = _
      congr 1
      funext k
      refine Fin.cases rfl (fun l => ?_) k
      exact Fin.cases rfl (fun m => Fin.elim0 m) l
    · refine Fin.cases rfl (fun k => ?_) j
      exact Fin.cases rfl (fun l => Fin.elim0 l) k
  have he : (Semiterm.val (L := language) ![ih,s] Empty.elim ∘
      PRAHistoryFixpointSuccCode.graphRew c ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he] at hm
  exact hm
end models

theorem PRA_proves_termStep (c : Code 2)
    (hc : PRA ⊢ PRAHistoryFixpointSuccCode.graphSentence (FormalizedTerm.blueprint ℒₛₑₜ) c) :
    PRA ⊢ stepGraphSentence termBlueprint (swapStep c) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  simp only [models_iff,stepGraphSentence,Semiformula.eval_allClosure]
  intro e
  rw [Matrix.fun_eq_vec_two e]
  simp only [Semiformula.eval_rew]
  have hv : (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘
      stepGraphRew (swapStep c) ∘ Semiterm.bvar) =
      ![Structure.func (L := language) c ![e 1,e 0],e 1,e 0] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) (swapStep c)
        (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘ ![#0,#1]) = _
      have hv : (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘ ![#0,#1]) = ![e 0,e 1] := by
        funext k
        refine Fin.cases rfl (fun l => ?_) k
        exact Fin.cases rfl (fun m => Fin.elim0 m) l
      rw [hv]
      exact modelSwapComposition c (e 0) (e 1)
    · refine Fin.cases rfl (fun k => ?_) j
      exact Fin.cases rfl (fun l => Fin.elim0 l) k
  have he : (Semiterm.val (L := language) ![e 0,e 1] Empty.elim ∘
      stepGraphRew (swapStep c) ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,he]
  exact modelTermSucc c hc (e 1) (e 0)

theorem PRA_has_setTermResultCode : ∃ step : Code 2,
    PRA ⊢ resultGraphSentence termBlueprint zeroCode step := by
  obtain ⟨nextCode,hsucc⟩ := PRAHistorySetTermCode.PRA_has_setTermSuccCode
  exact ⟨swapStep nextCode,PRA_proves_resultGraph termBlueprint zeroCode (swapStep nextCode)
    PRA_proves_termZero (PRA_proves_termStep nextCode hsucc)⟩
end DiophantineConsistency.PRAHistorySetTermResult
