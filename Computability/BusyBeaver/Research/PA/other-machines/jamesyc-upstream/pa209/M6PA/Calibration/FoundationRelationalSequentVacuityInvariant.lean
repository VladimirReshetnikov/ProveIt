module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentFreshness
public import M6PA.Calibration.FoundationRelationalCodeCoverage
@[expose] public section

/-! Exact accepted-certificate relation and full-PA vacuity induction invariant.
This module supplies guarded atom payloads but does not perform the induction. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCertificateEquivalence ActualCheckerBlueprint

attribute [local irreducible] ActualArithmeticGraph.graph translateGraph acceptedArrowGraph
noncomputable def vacuityGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “code c param p. ∃ a all, !translateGraph a param p ∧
    !(ActualArithmeticGraph.graph ActualHeadGraphs.universalExpr) all c a 0 0 ∧
    !acceptedArrowGraph code a all”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem vacuity_graph (code c param p : V) :
    vacuityGraph.val.Evalb ![code,c,param,p] ↔
      verifyValue code=wim (translate param p) (wal c (translate param p))+1 := by
  simp [vacuityGraph,translate_graph,ActualArithmeticGraph.graph_correct,
    acceptedArrow_graph,wal,universalValue,Matrix.comp_vecCons'']

attribute [local irreducible] vacuityGraph coverageGraph freshEnvironmentGraph parametersGraph
noncomputable def vacuityInvariant : ArithmeticSemisentence 1 :=
  “n. ∀ p<n, ∀ c b f lo z, !coverageGraph b f lo z p →
    !freshEnvironmentGraph c b f lo z →
    ∃ param code, !parametersGraph param b f lo z ∧ !vacuityGraph code c param p”

theorem vacuity_invariant (n : V) : vacuityInvariant.Evalb ![n] ↔
    ∀ p<n, ∀ c b f lo z : V, FormulaCovered b f lo z p → FreshEnvironment c b f lo z →
      ∃ code, verifyValue code=wim (translate (parameters b f lo z) p)
        (wal c (translate (parameters b f lo z) p))+1 := by
  simp [vacuityInvariant,coverage_graph,freshEnvironment_graph,parameters_graph,
    vacuity_graph,Matrix.comp_vecCons'']

/-- Guarded atom data provides exactly the three distinctness premises needed
by membership/neighborhood numeric vacuity recipes. -/
theorem fresh_atom_payload {c b f lo z k r ts : V}
    (h : ∃ y, AtomTranslation y k r ts b f lo z) (hf : FreshEnvironment c b f lo z) :
    ∃ a d, AtomHead (totalAtom (parameters b f lo z) k r ts) r a d z ∧
      c≠a ∧ c≠d ∧ c≠z := by
  obtain ⟨y,hy⟩ := h
  have he := totalAtom_agrees hy
  obtain ⟨hk,hlen,henv,a,d,ha,hd,hhead⟩ := hy
  exact ⟨a,d,he ▸ hhead,hf.label_ne ha,hf.label_ne hd,hf.2.1⟩

theorem fresh_rel_payload {c b f lo z k r ts : V}
    (h : FormulaCovered b f lo z (qqRel k r ts)) (hf : FreshEnvironment c b f lo z) :
    ∃ a d, AtomHead (totalAtom (parameters b f lo z) k r ts) r a d z ∧
      c≠a ∧ c≠d ∧ c≠z := fresh_atom_payload (coverage_rel_atom h) hf

theorem fresh_nrel_payload {c b f lo z k r ts : V}
    (h : FormulaCovered b f lo z (qqNRel k r ts)) (hf : FreshEnvironment c b f lo z) :
    ∃ a d, AtomHead (totalAtom (parameters b f lo z) k r ts) r a d z ∧
      c≠a ∧ c≠d ∧ c≠z := fresh_atom_payload (coverage_nrel_atom h) hf

#print axioms vacuity_graph
#print axioms vacuity_invariant
#print axioms fresh_atom_payload
#print axioms fresh_rel_payload
#print axioms fresh_nrel_payload
end M6.PA.RelationalSource.Numeric

