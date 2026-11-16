module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalCodeLanguage
@[expose] public section

/-! Guarded variable-label translation using finite HFS environments. This is
the variable/atom prerequisite, not a total formula or proof interpreter. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Out-of-range free variables are not silently assigned a default label. -/
def VariableLabel (y t b f : V) : Prop :=
  (∃ i < len b, t=qqBvar i ∧ y=nth b i) ∨
  (∃ i < len f, t=qqFvar i ∧ y=nth f i)

noncomputable def variableLabelGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y t b f. (∃ n, !lenDef n b ∧ ∃ i < n, !qqBvarDef t i ∧ !nthDef y b i) ∨
    (∃ n, !lenDef n f ∧ ∃ i < n, !qqFvarDef t i ∧ !nthDef y f i)”

theorem variableLabel_graph (y t b f : V) :
    variableLabelGraph.val.Evalb ![y,t,b,f] ↔ VariableLabel y t b f := by
  simp [variableLabelGraph,VariableLabel]

theorem label_bvar (b f i : V) (hi : i < len b) :
    VariableLabel (nth b i) (qqBvar i) b f := Or.inl ⟨i,hi,rfl,rfl⟩

theorem label_fvar (b f i : V) (hi : i < len f) :
    VariableLabel (nth f i) (qqFvar i) b f := Or.inr ⟨i,hi,rfl,rfl⟩

/-- Calibration is to Foundation's variable quotation, not native formula tags. -/
theorem label_quote_bvar {n : Nat} (i : Fin n) (b f : V) (hi : (i:V)<len b) :
    VariableLabel (nth b i) (⌜(#i : SyntacticSemiterm language n)⌝ : V) b f := by
  simpa using label_bvar b f (i:V) hi

theorem label_quote_fvar (i : Nat) {n : Nat} (b f : V) (hi : (i:V)<len f) :
    VariableLabel (nth f i) (⌜(&i : SyntacticSemiterm language n)⌝ : V) b f := by
  simpa using label_fvar b f (i:V) hi

theorem label_unique {y y' t b f : V}
    (h : VariableLabel y t b f) (h' : VariableLabel y' t b f) : y=y' := by
  rcases h with ⟨i,hi,ht,hy⟩ | ⟨i,hi,ht,hy⟩
  · rcases h' with ⟨j,hj,ht',hy'⟩ | ⟨j,hj,ht',hy'⟩
    · have hij : i=j := qqBvar_inj.mp (ht.symm.trans ht')
      subst j
      exact hy.trans hy'.symm
    · have he := ht.symm.trans ht'
      simp [qqBvar,qqFvar] at he
  · rcases h' with ⟨j,hj,ht',hy'⟩ | ⟨j,hj,ht',hy'⟩
    · have he := ht.symm.trans ht'
      simp [qqBvar,qqFvar] at he
    · have hij : i=j := qqFvar_inj.mp (ht.symm.trans ht')
      subst j
      exact hy.trans hy'.symm

/-- Well-formed variable terms, with a separately explicit free-environment
coverage condition. No host function is encoded by assumption. -/
def Covered (t b f : V) : Prop :=
  IsSemiterm language (len b) t ∧ ∀ i, t=qqFvar i → i<len f

theorem label_covered {y t b f : V} (h : VariableLabel y t b f) : Covered t b f := by
  rcases h with ⟨i,hi,rfl,_⟩ | ⟨i,hi,rfl,_⟩
  · refine ⟨(source_term_cases _ _).mpr (Or.inl ⟨i,hi,rfl⟩),?_⟩
    intro j he
    simp [qqBvar,qqFvar] at he
  · refine ⟨(source_term_cases _ _).mpr (Or.inr ⟨i,rfl⟩),?_⟩
    intro j he
    have hij := qqFvar_inj.mp he
    simpa [← hij] using hi

theorem label_exists_iff (t b f : V) :
    (∃ y, VariableLabel y t b f) ↔ Covered t b f := by
  constructor
  · rintro ⟨y,h⟩
    exact label_covered h
  · rintro ⟨ht,hf⟩
    rcases (source_term_cases _ _).mp ht with ⟨i,hi,rfl⟩ | ⟨i,rfl⟩
    · exact ⟨nth b i,label_bvar b f i hi⟩
    · exact ⟨nth f i,label_fvar b f i (hf i rfl)⟩

def EnvironmentsValid (b f lo z : V) : Prop :=
  0<lo ∧ lo≤z ∧ (∀ i<len b, nth b i<lo) ∧ ∀ i<len f, nth f i<lo

noncomputable def environmentsGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “b f lo z. 0<lo ∧ lo≤z ∧ ∃ nb nf, !lenDef nb b ∧ !lenDef nf f ∧
    (∀ i<nb, ∃ y, !nthDef y b i ∧ y<lo) ∧
    (∀ i<nf, ∃ y, !nthDef y f i ∧ y<lo)”

theorem environments_graph (b f lo z : V) :
    environmentsGraph.val.Evalb ![b,f,lo,z] ↔ EnvironmentsValid b f lo z := by
  simp [environmentsGraph,EnvironmentsValid]

theorem label_below {y t b f lo z : V}
    (h : VariableLabel y t b f) (he : EnvironmentsValid b f lo z) : y<lo := by
  rcases h with ⟨i,hi,_,rfl⟩ | ⟨i,hi,_,rfl⟩
  · exact he.2.2.1 i hi
  · exact he.2.2.2 i hi

theorem label_reserved {y t b f lo z : V}
    (h : VariableLabel y t b f) (he : EnvironmentsValid b f lo z) : y≠z :=
  ne_of_lt (lt_of_lt_of_le (label_below h he) he.2.1)

#print axioms variableLabel_graph
#print axioms label_quote_bvar
#print axioms label_quote_fvar
#print axioms label_unique
#print axioms label_covered
#print axioms label_exists_iff
#print axioms environments_graph
#print axioms label_below
#print axioms label_reserved
end M6.PA.RelationalSource.Numeric

