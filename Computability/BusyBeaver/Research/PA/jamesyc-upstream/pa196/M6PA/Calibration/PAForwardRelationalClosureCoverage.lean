module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalClosureIntroduction
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

theorem termOccurs_free_mem {n : Nat} (t : SourceTerm n) (i : Nat)
    (h : TermOccurs (.inr i) t) : t.FVar? i := by
  induction t with
  | bvar j => cases h
  | fvar j => cases h; simp [SourceVariable.term]
  | func fn ts ih =>
    cases h with
    | func j hj =>
      simp only [Semiterm.fvar?_func]
      exact ⟨j, ih j hj⟩

theorem formulaOccurs_free_mem {n : Nat} (p : SourceFormula n) (i : Nat)
    (h : FormulaOccurs (.inr i) p) : p.FVar? i := by
  induction p with
  | verum => cases h
  | falsum => cases h
  | rel r ts =>
    cases h with
    | rel j hj => exact Semiformula.fvar?_rel.mpr ⟨j, termOccurs_free_mem (ts j) i hj⟩
  | nrel r ts =>
    cases h with
    | nrel j hj => exact Semiformula.fvar?_nrel.mpr ⟨j, termOccurs_free_mem (ts j) i hj⟩
  | and p q ihp ihq =>
    cases h with
    | andLeft hp => simpa only [Semiformula.FVar?, Semiformula.freeVariables, Finset.mem_union] using Or.inl (ihp hp)
    | andRight hq => simpa only [Semiformula.FVar?, Semiformula.freeVariables, Finset.mem_union] using Or.inr (ihq hq)
  | or p q ihp ihq =>
    cases h with
    | orLeft hp => simpa only [Semiformula.FVar?, Semiformula.freeVariables, Finset.mem_union] using Or.inl (ihp hp)
    | orRight hq => simpa only [Semiformula.FVar?, Semiformula.freeVariables, Finset.mem_union] using Or.inr (ihq hq)
  | all p ih =>
    cases h with
    | all hp => exact ih hp
  | exs p ih =>
    cases h with
    | exs hp => exact ih hp

def formulaCoverageFromPrefix {Γ : List Form} (p : SourceFormula 0)
    (f : Nat → Term 0) (H : FiniteParameterDomains Γ p.fvSup f) :
    FormulaDomainCoverage Γ Fin.elim0 f p := by
  intro v hv
  cases v with
  | inl i => exact Fin.elim0 i
  | inr i =>
    exact H ⟨i, Semiformula.lt_fvSup_of_fvar? (formulaOccurs_free_mem p i hv)⟩

/-- The caller may provide proofs guarded only at actually occurring source
parameters; the finite closure prefix discharges that weaker body obligation. -/
def sourceUniversalClosureIntroOccurrences {Γ : List Form} (p : SourceFormula 0)
    (body : ∀ {Δ : List Form}, SubstitutionPremises Δ → ∀ f : Nat → Term 0,
      FormulaDomainCoverage Δ Fin.elim0 f p → ND.Proof Δ (formula p Fin.elim0 f))
    (A : SubstitutionPremises Γ) (f : Nat → Term 0) :
    ND.Proof Γ (formula p.univCl' Fin.elim0 f) :=
  sourceUniversalClosureIntro p (fun A' g H => body A' g (formulaCoverageFromPrefix p g H)) A f

#print axioms termOccurs_free_mem
#print axioms formulaOccurs_free_mem
#print axioms formulaCoverageFromPrefix
#print axioms sourceUniversalClosureIntroOccurrences
end M6.PA.ForwardRelational

