import DiophantineConsistency.PRAQOrder

/-! A fixed primitive-recursive witness for the candidate order relation. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAQOrderWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAExhaustion
  PRASubReconstruct PRAQOrder

def witnessTerm : TermN 2 :=
  applyCode predCode (fun _ => applyCode subCode ![.bvar 1, .bvar 0])

def witnessSentence : Sentence language :=
  ∀⁰* ((Semiformula.rel Language.ORing.Rel.lt ![.bvar 0, .bvar 1]) 🡒
    (Semiformula.rel Language.ORing.Rel.eq
      ![applyCode addCode ![.bvar 0, applyCode Code.succ (fun _ => witnessTerm)], .bvar 1]) :
    Semisentence language 2)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelWitness (x y : M)
    (hxy : Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]) :
    Structure.func (L := language) addCode
      ![x, Structure.func (L := language) Code.succ (fun _ =>
        Structure.func (L := language) predCode (fun _ =>
          Structure.func (L := language) subCode ![y,x]))] = y := by
  have hn := (modelLtDifference x y).mp hxy
  have hr := (modelReconstruct x y).resolve_left hn
  have hex := modelExhaustion (M := M)
  simp only [models_iff, exhaustionSentence, Semiformula.eval_univCl, Semiformula.eval_all] at hex
  let d := Structure.func (L := language) subCode ![y,x]
  have h := (body_eval d (fun _ => y)).mp (hex (fun _ => y) d)
  rw [h.resolve_left hn]
  exact hr

theorem modelWitnessSentence : M↓[language] ⊧ witnessSentence := by
  simp only [models_iff, witnessSentence, Semiformula.eval_allClosure]
  intro e
  change Semiformula.EvalAux (inferInstance : Structure language M) Empty.elim e _
  simp [Semiformula.EvalAux, Semiformula.neg, eqRel, applyCode, witnessTerm, Function.comp_def]
  have hrel : (fun i : Fin 2 => Semiterm.val e Empty.elim (![.bvar 0, .bvar 1] i : TermN 2)) =
      ![e 0, e 1] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have hadd : (fun i : Fin 2 => Semiterm.val e Empty.elim
      (![.bvar 0, .func Code.succ (fun _ => .func predCode
        (fun _ => .func subCode ![.bvar 1, .bvar 0]))] i : TermN 2)) =
      ![e 0, Structure.func (L := language) Code.succ (fun _ =>
        Structure.func (L := language) predCode (fun _ =>
          Structure.func (L := language) subCode ![e 1,e 0]))] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    simp only [Semiterm.val_func, Function.comp_def]
    trace_state
    sorry
  rw [hrel, hadd]
  by_cases hxy : Structure.rel (L := language) Language.ORing.Rel.lt ![e 0,e 1]
  · exact Or.inr (modelWitness (e 0) (e 1) hxy)
  · exact Or.inl hxy

end models

/-- Candidate PRA proves that the indicated fixed primitive-recursive term
produces an order witness for every pair of inputs. -/
theorem PRA_proves_orderWitness : PRA ⊢ witnessSentence := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact modelWitnessSentence

end DiophantineConsistency.PRAQOrderWitness
