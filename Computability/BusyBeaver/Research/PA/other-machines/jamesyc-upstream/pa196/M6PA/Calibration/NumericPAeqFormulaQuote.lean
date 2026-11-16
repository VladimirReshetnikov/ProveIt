module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaQuoteAtoms
@[expose] public section

/-! Exact calibration of the complete coded PAeq formula interpreter to the
unchanged typed relational interpretation, with explicit finite environment
agreement. This theorem concerns quoted host syntax, not proof-code transport. -/
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource.Ordinal (Term Formula)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem formulaSyntax_quote {s : Nat} (p : ForwardRelational.SourceFormula s) :
    ∀{m : Nat} (param : V) (b : Fin s → Term m) (f : Nat → Term m),
    ParametersValid (s:V) (m:V) param → BoundAgreement param b → FormulaFreeAgreement param p f →
    formulaSyntax param (⌜p⌝ : V)=⌜ForwardRelational.formula p b f⌝ := by
  induction p with
  | rel r ts =>
    intro m param b f h hb hf
    cases r with
    | eq =>
      change formulaSyntax param (qqRel 2 0 (quoteTerms ts))=_
      rw [formulaSyntax_rel _ _ _ _ (by simp)
        (by simpa only [quoteTerms,Nat.cast_ofNat] using!
          (SemitermVec.isUTermVec (fun j => (⌜ts j⌝ : Bootstrapping.Semiterm V Presentation.language _))))]
      apply atomCode_quote ts param b f h hb
      intro j i hi
      exact hf i (FFL.FirstOrder.Semiformula.fvar?_rel.mpr ⟨j,hi⟩)
  | nrel r ts =>
    intro m param b f h hb hf
    cases r with
    | eq =>
      change formulaSyntax param (qqNRel 2 0 (quoteTerms ts))=_
      rw [formulaSyntax_nrel _ _ _ _ (by simp)
        (by simpa only [quoteTerms,Nat.cast_ofNat] using!
          (SemitermVec.isUTermVec (fun j => (⌜ts j⌝ : Bootstrapping.Semiterm V Presentation.language _)))),
        atomCode_quote ts param b f h hb (fun j i hi => hf i (FFL.FirstOrder.Semiformula.fvar?_nrel.mpr ⟨j,hi⟩))]
      simp [ForwardRelational.formula,←FFL.FirstOrder.Semiformula.neg_eq,FFL.FirstOrder.Semiformula.quote_def]
  | verum =>
    intro m param b f h hb hf
    exact formulaSyntax_verum _
  | falsum =>
    intro m param b f h hb hf
    exact formulaSyntax_falsum _
  | and p q ihp ihq =>
    intro m param b f h hb hf
    change formulaSyntax param (qqAnd (⌜p⌝ : V) (⌜q⌝ : V))=_
    rw [formulaSyntax_and _ _ _ (FFL.FirstOrder.Semiformula.quote_isSemiformula p).isUFormula
      (FFL.FirstOrder.Semiformula.quote_isSemiformula q).isUFormula,
      ihp param b f h hb (fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_and i p q).mpr (Or.inl hi))),
      ihq param b f h hb (fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_and i p q).mpr (Or.inr hi)))]
    rfl
  | or p q ihp ihq =>
    intro m param b f h hb hf
    change formulaSyntax param (qqOr (⌜p⌝ : V) (⌜q⌝ : V))=_
    rw [formulaSyntax_or _ _ _ (FFL.FirstOrder.Semiformula.quote_isSemiformula p).isUFormula
      (FFL.FirstOrder.Semiformula.quote_isSemiformula q).isUFormula,
      ihp param b f h hb (fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_or i p q).mpr (Or.inl hi))),
      ihq param b f h hb (fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_or i p q).mpr (Or.inr hi)))]
    rfl
  | all p ih =>
    intro m param b f h hb hf
    change formulaSyntax param (qqAll (⌜p⌝ : V))=_
    rw [formulaSyntax_all _ _ (FFL.FirstOrder.Semiformula.quote_isSemiformula p).isUFormula]
    have hi := ih (binderParameters param) (ForwardRelational.bindEnv b) (ForwardRelational.shiftEnv f)
      (by simpa using binderParameters_valid h) (binder_bound_agreement b h hb)
      (formulaFreeAgreement_binder p f h (fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_all i p).mpr hi)))
    rw [hi,guardedAllCode_quote]
    rfl
  | exs p ih =>
    intro m param b f h hb hf
    change formulaSyntax param (qqExs (⌜p⌝ : V))=_
    rw [formulaSyntax_exs _ _ (FFL.FirstOrder.Semiformula.quote_isSemiformula p).isUFormula]
    have hi := ih (binderParameters param) (ForwardRelational.bindEnv b) (ForwardRelational.shiftEnv f)
      (by simpa using binderParameters_valid h) (binder_bound_agreement b h hb)
      (formulaFreeAgreement_binder p f h (fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_exs i p).mpr hi)))
    rw [hi,guardedExsCode_quote]
    rfl

#print axioms formulaSyntax_quote
end M6.PA.NumericPAeqFormula

