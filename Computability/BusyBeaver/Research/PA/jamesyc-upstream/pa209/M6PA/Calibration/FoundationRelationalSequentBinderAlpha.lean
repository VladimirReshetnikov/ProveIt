module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentRename
public import M6PA.Calibration.ActualCertificateNeighborhoodSpecialization
@[expose] public section

/-! Source bound-head alpha with a common body allocator and reserve. Both
eigenlabels explicitly avoid the old finite environments. No allocator change. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCertificateEquivalence ActualCheckerBlueprint

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem FreshEnvironment.adjoin_avoiding {c b f lo z a : V}
    (h : FreshEnvironment c b f lo z) (ha : c≠a) : FreshEnvironment c (a∷b) f lo z := by
  refine ⟨h.1,h.2.1,?_,h.2.2.2⟩
  intro i hi
  rcases zero_or_succ i with rfl | ⟨i,rfl⟩
  · simpa using ha
  · have hi' : i<len b := by simpa using hi
    simpa using h.2.2.1 i hi'

variable [V↓[ℒₒᵣ] ⊧* theory]

theorem bound_head_alpha_certificates (p x y b f lo z : V)
    (hc : FormulaCovered (x∷b) f lo z p)
    (hx : FreshEnvironment x b f lo z) (hy : FreshEnvironment y b f lo z) :
    ∃ forward backward, BiCertificates forward backward
      (wal x (translate (parameters (x∷b) f lo z) p))
      (wal y (translate (parameters (y∷b) f lo z) p)) := by
  by_cases hxy : x=y
  · subst y
    exact ⟨_,_,(BiWitness.refl _).accepted⟩
  have hb : RenameEnvironment x y (x∷b) (y∷b) := renameEnvironment_head hx.2.2.1
  have hf : RenameEnvironment x y f f := renameEnvironment_fixed hx.2.2.2
  have hc' := coverage_rename hb hf hc hy.1
  obtain ⟨forward,backward,hforward,hbackward⟩ :=
    formula_rename_certificates p x y (x∷b) (y∷b) f f lo z hc hb hf hx.1 hy.1
  obtain ⟨bx,hbx⟩ := formula_vacuity_certificate p x (y∷b) f lo z hc' (hx.adjoin_avoiding hxy)
  obtain ⟨ay,hay⟩ := formula_vacuity_certificate p y (x∷b) f lo z hc (hy.adjoin_avoiding (Ne.symm hxy))
  let out := universalAlphaNeighborhood x y z
    (translate (parameters (x∷b) f lo z) p) (translate (parameters (y∷b) f lo z) p)
    (Ne.symm hx.2.1) (Ne.symm hy.2.1) ⟨forward,hforward⟩ ⟨backward,hbackward⟩ ⟨bx,hbx⟩ ⟨ay,hay⟩
  exact ⟨out.1.code,out.2.code,out.1.accepted,out.2.accepted⟩

attribute [local irreducible] parametersGraph translateGraph ActualArithmeticGraph.graph biGraph
noncomputable def boundHeadAlphaGraph : 𝚺ᴬ₁.Semisentence 9 := .mkSigma
  “forward backward p x y b f lo z. ∃ xb yb param target a aa allx ally,
    !adjoinDef xb x b ∧ !adjoinDef yb y b ∧
    !parametersGraph param xb f lo z ∧ !parametersGraph target yb f lo z ∧
    !translateGraph a param p ∧ !translateGraph aa target p ∧
    !(ActualArithmeticGraph.graph ActualHeadGraphs.universalExpr) allx x a 0 0 ∧
    !(ActualArithmeticGraph.graph ActualHeadGraphs.universalExpr) ally y aa 0 0 ∧
    !biGraph forward backward allx ally”

theorem boundHeadAlpha_graph (forward backward p x y b f lo z : V) :
    boundHeadAlphaGraph.val.Evalb ![forward,backward,p,x,y,b,f,lo,z] ↔
      BiCertificates forward backward (wal x (translate (parameters (x∷b) f lo z) p))
        (wal y (translate (parameters (y∷b) f lo z) p)) := by
  simp [boundHeadAlphaGraph,parameters_graph,translate_graph,ActualArithmeticGraph.graph_correct,
    bi_graph,wal,universalValue,Matrix.comp_vecCons'']

attribute [local irreducible] boundHeadAlphaGraph coverageGraph freshEnvironmentGraph
noncomputable def boundHeadAlphaSentence : ArithmeticSentence :=
  “∀ p x y b f lo z, !freshEnvironmentGraph x b f lo z → !freshEnvironmentGraph y b f lo z →
    ∀ xb, !adjoinDef xb x b → !coverageGraph xb f lo z p →
      ∃ forward backward, !boundHeadAlphaGraph forward backward p x y b f lo z”

theorem pa_proves_boundHeadAlpha : theory ⊢ boundHeadAlphaSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [boundHeadAlphaSentence,models_iff,freshEnvironment_graph,coverage_graph,
    boundHeadAlpha_graph,Matrix.comp_vecCons'']
  intro p x y b f lo z hx hy hc
  exact bound_head_alpha_certificates p x y b f lo z hc hx hy

#print axioms FreshEnvironment.adjoin_avoiding
#print axioms bound_head_alpha_certificates
#print axioms boundHeadAlpha_graph
#print axioms pa_proves_boundHeadAlpha
end M6.PA.RelationalSource.Numeric

