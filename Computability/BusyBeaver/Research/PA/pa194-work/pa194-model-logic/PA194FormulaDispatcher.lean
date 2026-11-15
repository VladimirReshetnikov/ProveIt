import PA194AtomicPAeq
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

noncomputable def formulaChildParameters (param : V) : V :=
  parameters ((^#(0 : V)) ∷ shiftTerms (nth param 0))
    (shiftTerms (nth param 1)) (termBShift SourceL (nth param 2))
noncomputable def formulaChildParametersGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out param. ∃ b f z bs fs zs x bnew,
    !nthDef b param 0 ∧ !nthDef f param 1 ∧ !nthDef z param 2 ∧
    !shiftTermsGraph bs b ∧ !shiftTermsGraph fs f ∧ !(termBShiftGraph SourceL) zs z ∧
    !qqBvarDef x 0 ∧ !adjoinDef bnew x bs ∧ !parametersGraph out bnew fs zs”
theorem formulaChildParameters_graph (out param : V) :
    formulaChildParametersGraph.val.Evalb ![out,param] ↔ out = formulaChildParameters param := by
  simp [formulaChildParametersGraph,formulaChildParameters,shiftTerms_graph,parameters_graph,Matrix.comp_vecCons'']
instance formulaChildParameters_defined : 𝚺₁-Function₁ (formulaChildParameters : V → V) via formulaChildParametersGraph := .mk fun v => by
  change formulaChildParametersGraph.val.Evalb v ↔ v 0 = formulaChildParameters (v 1)
  have hv : ![v 0,v 1] = v := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  simpa only [hv] using formulaChildParameters_graph (v 0) (v 1)

theorem formulaChildParameters_valid {s n param : V} (h : ParametersValid s n param) :
    ParametersValid (s+1) (n+1) (formulaChildParameters param) := by
  rcases h with ⟨hb,hf,hz⟩
  unfold ParametersValid formulaChildParameters
  simp only [parameters_bound,parameters_free,parameters_result]
  refine ⟨(shiftTerms_valid hb).adjoin (by simp),?_,?_⟩
  · simpa [shiftTerms_length hf] using shiftTerms_valid hf
  · simpa using hz.bShift

noncomputable def atom (param v : V) : V := atomicEquality param (nth v 0) (nth v 1)
noncomputable def allOutput (child : V) : V :=
  ^∀ (imp SourceL (domainCode (^#(0 : V))) child)
noncomputable def exsOutput (child : V) : V :=
  ^∃ (domainCode (^#(0 : V)) ^⋏ child)

noncomputable def formulaBlueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “out param k R v. ∃ a b, !nthDef a v 0 ∧ !nthDef b v 1 ∧ !atomicEqualityGraph out param a b”
  nrel := .mkSigma “out param k R v. ∃ a b eq, !nthDef a v 0 ∧ !nthDef b v 1 ∧ !atomicEqualityGraph eq param a b ∧ !(negGraph SourceL) out eq”
  verum := .mkSigma “out param. !qqVerumDef out”
  falsum := .mkSigma “out param. !qqFalsumDef out”
  and := .mkSigma “out param p q l r. !qqAndDef out l r”
  or := .mkSigma “out param p q l r. !qqOrDef out l r”
  all := .mkSigma “out param p child. ∃ b d inner, !qqBvarDef b 0 ∧ !(templateOneGraph domainTemplate) d b ∧ !(impGraph SourceL) inner d child ∧ !qqAllDef out inner”
  exs := .mkSigma “out param p child. ∃ b d inner, !qqBvarDef b 0 ∧ !(templateOneGraph domainTemplate) d b ∧ !qqAndDef inner d child ∧ !qqExsDef out inner”
  allChanges := .mkSigma “out param. !formulaChildParametersGraph out param”
  exsChanges := .mkSigma “out param. !formulaChildParametersGraph out param”
noncomputable def formulaConstruction : UformulaRec1.Construction V formulaBlueprint where
  rel param _ _ v := atom param v
  nrel param _ _ v := neg SourceL (atom param v)
  verum _ := ^⊤
  falsum _ := ^⊥
  and _ _ _ l r := l ^⋏ r
  or _ _ _ l r := l ^⋎ r
  all _ _ child := allOutput child
  exs _ _ child := exsOutput child
  allChanges param := formulaChildParameters param
  exsChanges param := formulaChildParameters param
  rel_defined := .mk fun v => by simp [formulaBlueprint,atom,atomicEquality_graph,Matrix.comp_vecCons'']
  nrel_defined := .mk fun v => by simp [formulaBlueprint,atom,atomicEquality_graph,Matrix.comp_vecCons'']
  verum_defined := .mk fun v => by simp [formulaBlueprint]
  falsum_defined := .mk fun v => by simp [formulaBlueprint]
  and_defined := .mk fun v => by simp [formulaBlueprint]
  or_defined := .mk fun v => by simp [formulaBlueprint]
  all_defined := .mk fun v => by simp [formulaBlueprint,allOutput,domainCode,Matrix.comp_vecCons'']
  exs_defined := .mk fun v => by simp [formulaBlueprint,exsOutput,domainCode,Matrix.comp_vecCons'']
  allChanges_defined := .mk fun v => by simp [formulaBlueprint,formulaChildParameters_graph,Matrix.comp_vecCons'']
  exChanges_defined := .mk fun v => by simp [formulaBlueprint,formulaChildParameters_graph,Matrix.comp_vecCons'']
noncomputable def translateFormula (param p : V) : V :=
  (formulaConstruction (V := V)).result PA194PAeq.language param p
noncomputable def translateFormulaGraph : 𝚺₁.Semisentence 3 := formulaBlueprint.result PA194PAeq.language
theorem translateFormula_graph (out param p : V) :
    translateFormulaGraph.val.Evalb ![out,param,p] ↔ out = translateFormula param p := by
  simpa [translateFormulaGraph,translateFormula] using (formulaConstruction (V := V)).result_defined.defined ![out,param,p]
#print axioms formulaChildParameters_valid
#print axioms translateFormula_graph
end generic
end PA194FormulaDispatcher
