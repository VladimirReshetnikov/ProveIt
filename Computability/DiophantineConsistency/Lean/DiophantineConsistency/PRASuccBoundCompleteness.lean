import DiophantineConsistency.PRAIOpenCompleteness
set_option autoImplicit false
namespace DiophantineConsistency.PRASuccBoundCompleteness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

/-- A two-variable arithmetic implication with an explicit successor witness
bound yields the corresponding universally closed candidate-PRA sentence. -/
theorem proves_succ_bound (φ : ArithmeticSemisentence 2) (ψ : ArithmeticSemisentence 3)
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (x p : M),
      φ.Eval ![x,p] Empty.elim → ψ.Eval ![x,p,p+1] Empty.elim) :
    PRA ⊢ ∀⁰* ((Semiformula.lMap embedding φ) 🡒
      (Rew.subst ![#0, #1, applyCode addCode ![#1, applyCode oneCode Fin.elim0]] ▹
        Semiformula.lMap embedding ψ)) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  simp only [models_iff, Semiformula.eval_allClosure]
  intro e
  simp only [LogicalConnective.HomClass.map_imply]
  intro he
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  have he' : (Semiformula.lMap embedding φ).Eval ![e 0,e 1] Empty.elim := by
    have hv : ![e 0,e 1] = e := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      exact Fin.cases rfl (fun j => Fin.elim0 j) j
    rw [hv]
    exact he
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hb : (Semiformula.lMap embedding ψ).Eval ![e 0,e 1,e 1+1] Empty.elim := by
    rw [Semiformula.eval_lMap, reduct_eq_standard]
    apply h M (e 0) (e 1)
    rw [Semiformula.eval_lMap, reduct_eq_standard] at he'
    exact he'
  simp only [Semiformula.eval_rew]
  have hv : (Semiterm.val e Empty.elim ∘
        (Rew.subst ![#0, #1, applyCode addCode ![#1, applyCode oneCode Fin.elim0]]) ∘ Semiterm.bvar) =
      ![e 0, e 1, e 1+1] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun j => ?_) j
    refine Fin.cases ?_ (fun j => Fin.elim0 j) j
    simp [Function.comp_def, Rew.subst, applyCode, Semiterm.val_func]
    congr 1
    funext k
    refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases ?_ (fun k => Fin.elim0 k) k
    change Structure.func (L := language) oneCode
      (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 2)) =
      Structure.func (L := language) oneCode Fin.elim0
    congr 1
    exact Subsingleton.elim _ _
  have hf : (Semiterm.val e Empty.elim ∘
        (Rew.subst ![#0, #1, applyCode addCode ![#1, applyCode oneCode Fin.elim0]]) ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,hf]
  exact hb
end DiophantineConsistency.PRASuccBoundCompleteness
