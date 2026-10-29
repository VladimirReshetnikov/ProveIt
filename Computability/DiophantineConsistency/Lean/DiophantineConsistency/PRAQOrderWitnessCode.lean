import DiophantineConsistency.PRAQOrderWitness

/-! A single primitive-recursive function symbol for the order witness. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAQOrderWitnessCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAQOrderWitness

def witnessCode : Code 2 := .comp predCode
  (.cons (.comp subCode (.cons (.proj 1) (.cons (.proj 0) (.nil 2)))) (.nil 2))

def codeWitnessSentence : Sentence language :=
  ∀⁰* ((Semiformula.rel Language.ORing.Rel.lt ![.bvar 0, .bvar 1]) 🡒
    (Semiformula.rel Language.ORing.Rel.eq
      ![applyCode addCode ![.bvar 0,
        applyCode Code.succ (fun _ => applyCode witnessCode ![.bvar 0, .bvar 1])], .bvar 1]) :
    Semisentence language 2)

theorem witnessCode_primrec : Primrec (eval witnessCode) := eval_primrec witnessCode

theorem eval_witnessCode (x y : ℕ) :
    eval witnessCode (x ::ᵥ y ::ᵥ List.Vector.nil) = (y-x).pred := by
  change eval predCode (eval subCode (y ::ᵥ x ::ᵥ List.Vector.nil) ::ᵥ List.Vector.nil) = _
  rw [eval_subCode, eval_predCode]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelWitnessCode (x y : M) :
    Structure.func (L := language) witnessCode ![x,y] =
      Structure.func (L := language) predCode (fun _ =>
        Structure.func (L := language) subCode ![y,x]) :=
  PRAQOrder.modelUnaryAfterSwap predCode subCode x y

theorem modelWitnessByCode (x y : M)
    (hxy : Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]) :
    Structure.func (L := language) addCode
      ![x, Structure.func (L := language) Code.succ (fun _ =>
        Structure.func (L := language) witnessCode ![x,y])] = y := by
  rw [modelWitnessCode]
  exact modelWitness x y hxy

theorem modelCodeWitnessSentence : M↓[language] ⊧ codeWitnessSentence := by
  simp only [models_iff, codeWitnessSentence, Semiformula.eval_allClosure]
  intro e
  change Semiformula.EvalAux (inferInstance : Structure language M) Empty.elim e _
  simp [Semiformula.EvalAux, Semiformula.neg, eqRel, applyCode, Function.comp_def]
  have hrel : (fun i : Fin 2 => Semiterm.val e Empty.elim (![.bvar 0, .bvar 1] i : TermN 2)) =
      ![e 0, e 1] := by
    simpa only [Function.comp_def, Semiterm.val_bvar] using
      val_term_pair e (.bvar 0) (.bvar 1)
  have hadd : (fun i : Fin 2 => Semiterm.val e Empty.elim
      (![.bvar 0, .func Code.succ (fun _ => .func witnessCode ![.bvar 0, .bvar 1])] i : TermN 2)) =
      ![e 0, Structure.func (L := language) Code.succ (fun _ =>
        Structure.func (L := language) witnessCode ![e 0,e 1])] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    change Structure.func (L := language) Code.succ
      (fun _ => Structure.func (L := language) witnessCode
        (fun i => Semiterm.val e Empty.elim (![.bvar 0, .bvar 1] i : TermN 2))) = _
    rw [hrel]
    rfl
  rw [hrel, hadd]
  by_cases hxy : Structure.rel (L := language) Language.ORing.Rel.lt ![e 0,e 1]
  · exact Or.inr (modelWitnessByCode (e 0) (e 1) hxy)
  · exact Or.inl hxy

end models

/-- Candidate PRA proves its fixed PR witness symbol witnesses strict order. -/
theorem PRA_proves_orderWitnessCode : PRA ⊢ codeWitnessSentence := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact modelCodeWitnessSentence
end DiophantineConsistency.PRAQOrderWitnessCode
