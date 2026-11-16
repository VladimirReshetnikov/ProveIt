import PA194TranslatedSequent
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194FormulaDispatcher
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem translatedSequent_insert (param p source : V) :
    translatedSequent param (insert p source) = insert (translateFormula param p) (translatedSequent param source) := by
  apply mem_ext
  intro x
  simp only [translatedSequent_mem,mem_bitInsert_iff]
  constructor
  · rintro ⟨q,(rfl | hq),rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨q,hq,rfl⟩
  · rintro (rfl | ⟨q,hq,rfl⟩)
    · exact ⟨p,Or.inl rfl,rfl⟩
    · exact ⟨q,Or.inr hq,rfl⟩

noncomputable def compileVerum (param source : V) : V := verumIntro (translatedSequent param source)
noncomputable def compileVerumGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out param source. ∃ target, !translatedSequentGraph target param source ∧ !verumIntroGraph out target”
theorem compileVerum_graph (out param source : V) :
    compileVerumGraph.val.Evalb ![out,param,source] ↔ out = compileVerum param source := by
  simp [compileVerumGraph,compileVerum,translatedSequent_graph,Matrix.comp_vecCons'']

noncomputable def compileAnd (param source p q dp dq : V) : V :=
  andIntro (translatedSequent param source) (translateFormula param p) (translateFormula param q) dp dq
noncomputable def compileAndGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “out param source p q dp dq. ∃ target a b, !translatedSequentGraph target param source ∧
    !translateFormulaGraph a param p ∧ !translateFormulaGraph b param q ∧ !andIntroGraph out target a b dp dq”
theorem compileAnd_graph (out param source p q dp dq : V) :
    compileAndGraph.val.Evalb ![out,param,source,p,q,dp,dq] ↔ out = compileAnd param source p q dp dq := by
  simp [compileAndGraph,compileAnd,translatedSequent_graph,translateFormula_graph,Matrix.comp_vecCons'']

noncomputable def compileOr (param source p q dp : V) : V :=
  orIntro (translatedSequent param source) (translateFormula param p) (translateFormula param q) dp
noncomputable def compileOrGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out param source p q dp. ∃ target a b, !translatedSequentGraph target param source ∧
    !translateFormulaGraph a param p ∧ !translateFormulaGraph b param q ∧ !orIntroGraph out target a b dp”
theorem compileOr_graph (out param source p q dp : V) :
    compileOrGraph.val.Evalb ![out,param,source,p,q,dp] ↔ out = compileOr param source p q dp := by
  simp [compileOrGraph,compileOr,translatedSequent_graph,translateFormula_graph,Matrix.comp_vecCons'']

variable (T : Theory SourceL) [T.Δ₁]
theorem compileVerum_valid {param source : V} (hparam : ParametersValid 0 0 param)
    (hsource : IsFormulaSet PA194PAeq.language source)
    (hlen : ∀ p ∈ source, p < len (nth param 1)) (hp : (^⊤ : V) ∈ source) :
    Derivation T (compileVerum param source) := by
  apply Derivation.verumIntro (translatedSequent_valid hparam hsource hlen)
  have hmem : translateFormula param ^⊤ ∈ translatedSequent param source := translatedSequent_mem.mpr ⟨^⊤,hp,rfl⟩
  simpa [translate_verum] using hmem

theorem compileAnd_valid {param source p q dp dq : V} (hpq : p ^⋏ q ∈ source)
    (hsource : IsFormulaSet PA194PAeq.language source)
    (hdp : DerivationOf T dp (translatedSequent param (insert p source)))
    (hdq : DerivationOf T dq (translatedSequent param (insert q source))) :
    Derivation T (compileAnd param source p q dp dq) := by
  have hscope := (IsSemiformula.and).mp (hsource _ hpq)
  have hmem : translateFormula param (p ^⋏ q) ∈ translatedSequent param source := translatedSequent_mem.mpr ⟨p ^⋏ q,hpq,rfl⟩
  rw [translate_and param p q hscope.1.isUFormula hscope.2.isUFormula] at hmem
  apply Derivation.andIntro (T := T) hmem
  · simpa [translatedSequent_insert] using hdp
  · simpa [translatedSequent_insert] using hdq

theorem compileOr_valid {param source p q dp : V} (hpq : p ^⋎ q ∈ source)
    (hsource : IsFormulaSet PA194PAeq.language source)
    (hdp : DerivationOf T dp (translatedSequent param (insert p (insert q source)))) :
    Derivation T (compileOr param source p q dp) := by
  have hscope := (IsSemiformula.or).mp (hsource _ hpq)
  have hmem : translateFormula param (p ^⋎ q) ∈ translatedSequent param source := translatedSequent_mem.mpr ⟨p ^⋎ q,hpq,rfl⟩
  rw [translate_or param p q hscope.1.isUFormula hscope.2.isUFormula] at hmem
  apply Derivation.orIntro (T := T) hmem
  simpa [translatedSequent_insert] using hdp

theorem compileAnd_sequent (param source p q dp dq : V) :
    fstIdx (compileAnd param source p q dp dq) = translatedSequent param source := by simp [compileAnd]
theorem compileOr_sequent (param source p q dp : V) :
    fstIdx (compileOr param source p q dp) = translatedSequent param source := by simp [compileOr]
theorem compileVerum_sequent (param source : V) :
    fstIdx (compileVerum param source) = translatedSequent param source := by simp [compileVerum]
#print axioms translatedSequent_insert
#print axioms compileVerum_graph
#print axioms compileAnd_graph
#print axioms compileOr_graph
#print axioms compileVerum_valid
#print axioms compileAnd_valid
#print axioms compileOr_valid
end generic
end PA194FormulaDispatcher
