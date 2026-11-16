import PA194TranslatedAxiomContext
import ConPASetSequent
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194FormulaDispatcher
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open ConPA.Sequent
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def formulaTr : Tr V where
  tr := translateFormula
  trDef := translateFormulaGraph
  tr_defined := translateFormula_defined
noncomputable def translatedSequent (param source : V) : V := vecToSet (setList formulaTr param source)
noncomputable def translatedSequentGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out param source. ∃ v, !(enumLDef translateFormulaGraph) v param source source ∧ !vecToSetDef out v”
theorem translatedSequent_graph (out param source : V) :
    translatedSequentGraph.val.Evalb ![out,param,source] ↔ out = translatedSequent param source := by
  haveI : 𝚺₁-Function₃ (enumL (formulaTr (V := V))) via enumLDef translateFormulaGraph := enumL_defined formulaTr
  simp [translatedSequentGraph,translatedSequent,setList,formulaTr,Matrix.comp_vecCons'']
instance translatedSequent_defined : 𝚺₁-Function₂ (translatedSequent : V → V → V) via translatedSequentGraph := .mk fun v => by
  change translatedSequentGraph.val.Evalb v ↔ v 0 = translatedSequent (v 1) (v 2)
  have hv : ![v 0,v 1,v 2] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
        rfl
  simpa only [hv] using translatedSequent_graph (v 0) (v 1) (v 2)

theorem translatedSequent_mem {param source q : V} :
    q ∈ translatedSequent param source ↔ ∃ p ∈ source, q = translateFormula param p := by
  rw [translatedSequent,mem_vecToSet_iff]
  constructor
  · rintro ⟨i,hi,rfl⟩
    obtain ⟨p,hps,h⟩ := setList_sound formulaTr param source i hi
    exact ⟨p,hps,h⟩
  · rintro ⟨p,hps,rfl⟩
    obtain ⟨i,hi,h⟩ := setList_complete formulaTr param source hps
    exact ⟨i,hi,h.symm⟩

theorem translatedSequent_valid {param source : V} (hparam : ParametersValid 0 0 param)
    (hsource : IsFormulaSet PA194PAeq.language source)
    (hlen : ∀ p ∈ source, p < len (nth param 1)) :
    IsFormulaSet SourceL (translatedSequent param source) := by
  intro q hq
  obtain ⟨p,hps,rfl⟩ := translatedSequent_mem.mp hq
  exact formula_scope_translate (hsource p hps).isUFormula 0 0 param (hsource p hps) hparam (hlen p hps)

noncomputable def compileAxiom (param source p : V) : V :=
  contextAxiomDerivation param p (translatedSequent param source)
noncomputable def compileAxiomGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “out param source p. ∃ target, !translatedSequentGraph target param source ∧ !contextAxiomDerivationGraph out param p target”
theorem compileAxiom_graph (out param source p : V) :
    compileAxiomGraph.val.Evalb ![out,param,source,p] ↔ out = compileAxiom param source p := by
  simp [compileAxiomGraph,compileAxiom,translatedSequent_graph,contextAxiomDerivation_graph,Matrix.comp_vecCons'']
instance compileAxiom_defined : 𝚺₁-Function₃ (compileAxiom : V → V → V → V) via compileAxiomGraph := .mk fun v => by
  change compileAxiomGraph.val.Evalb v ↔ v 0 = compileAxiom (v 1) (v 2) (v 3)
  have hv : ![v 0,v 1,v 2,v 3] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => ?_) j
        · rfl
        · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  simpa only [hv] using compileAxiom_graph (v 0) (v 1) (v 2) (v 3)

variable (T : Theory SourceL) [T.Δ₁]
theorem compileAxiom_valid {param source p : V}
    (hparam : ParametersValid 0 0 param) (hsource : IsFormulaSet PA194PAeq.language source)
    (hlen : ∀ q ∈ source, q < len (nth param 1))
    (hp : p ∈ source) (hnp : neg PA194PAeq.language p ∈ source) :
    Derivation T (compileAxiom param source p) := by
  apply contextAxiomDerivation_valid T (hsource p hp) hparam (hlen p hp) (hlen _ hnp)
    (translatedSequent_valid hparam hsource hlen)
  · exact translatedSequent_mem.mpr ⟨p,hp,rfl⟩
  · exact translatedSequent_mem.mpr ⟨_,hnp,rfl⟩
theorem compileAxiom_sequent (param source p : V) :
    fstIdx (compileAxiom param source p) = translatedSequent param source := by
  simp [compileAxiom,contextAxiomDerivation_sequent]
#print axioms translatedSequent_graph
#print axioms translatedSequent_mem
#print axioms translatedSequent_valid
#print axioms compileAxiom_graph
#print axioms compileAxiom_valid
#print axioms compileAxiom_sequent
end generic
end PA194FormulaDispatcher
