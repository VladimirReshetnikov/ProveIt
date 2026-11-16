import PA194TranslatedConnectives
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
theorem translatedSequent_subset {param source source' : V} (h : source' ⊆ source) :
    translatedSequent param source' ⊆ translatedSequent param source := by
  intro q hq
  obtain ⟨p,hp,rfl⟩ := translatedSequent_mem.mp hq
  exact translatedSequent_mem.mpr ⟨p,h hp,rfl⟩
noncomputable def compileWeak (param source d : V) : V := wkRule (translatedSequent param source) d
noncomputable def compileWeakGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “out param source d. ∃ target, !translatedSequentGraph target param source ∧ !wkRuleGraph out target d”
theorem compileWeak_graph (out param source d : V) :
    compileWeakGraph.val.Evalb ![out,param,source,d] ↔ out = compileWeak param source d := by
  simp [compileWeakGraph,compileWeak,translatedSequent_graph,Matrix.comp_vecCons'']
noncomputable def compileCut (param source p d1 d2 : V) : V :=
  cutRule (translatedSequent param source) (translateFormula param p) d1 d2
noncomputable def compileCutGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out param source p d1 d2. ∃ target a, !translatedSequentGraph target param source ∧
    !translateFormulaGraph a param p ∧ !cutRuleGraph out target a d1 d2”
theorem compileCut_graph (out param source p d1 d2 : V) :
    compileCutGraph.val.Evalb ![out,param,source,p,d1,d2] ↔ out = compileCut param source p d1 d2 := by
  simp [compileCutGraph,compileCut,translatedSequent_graph,translateFormula_graph,Matrix.comp_vecCons'']
variable (T : Theory SourceL) [T.Δ₁]
theorem compileWeak_valid {param source source' d : V}
    (hparam : ParametersValid 0 0 param) (hsource : IsFormulaSet PA194PAeq.language source)
    (hlen : ∀ p ∈ source, p < len (nth param 1)) (hsubset : source' ⊆ source)
    (hd : DerivationOf T d (translatedSequent param source')) :
    Derivation T (compileWeak param source d) := by
  exact Derivation.wkRule (translatedSequent_valid hparam hsource hlen) (translatedSequent_subset hsubset) hd

theorem compileCut_valid {param source p d1 d2 : V}
    (hscope : IsSemiformula PA194PAeq.language 0 p) (hparam : ParametersValid 0 0 param)
    (hlen : p < len (nth param 1)) (hnlen : neg PA194PAeq.language p < len (nth param 1))
    (hd1 : DerivationOf T d1 (translatedSequent param (insert p source)))
    (hd2 : DerivationOf T d2 (translatedSequent param (insert (neg PA194PAeq.language p) source))) :
    Derivation T (compileCut param source p d1 d2) := by
  have heq := translateFormula_neg hscope.isUFormula 0 0 param hscope hparam hlen hnlen
  apply Derivation.cutRule (T := T)
  · simpa [translatedSequent_insert] using hd1
  · simpa [translatedSequent_insert,heq] using hd2

theorem compileWeak_sequent (param source d : V) :
    fstIdx (compileWeak param source d) = translatedSequent param source := by simp [compileWeak]
theorem compileCut_sequent (param source p d1 d2 : V) :
    fstIdx (compileCut param source p d1 d2) = translatedSequent param source := by simp [compileCut]
#print axioms translatedSequent_subset
#print axioms compileWeak_graph
#print axioms compileWeak_valid
#print axioms compileCut_graph
#print axioms compileCut_valid
end generic
end PA194FormulaDispatcher
