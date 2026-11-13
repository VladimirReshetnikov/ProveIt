module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentRenameAtoms
@[expose] public section

/-! Exact source-environment conditional renaming relation, displayed model
induction invariant, and guarded atomic certificate supply. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCertificateEquivalence ActualCheckerBlueprint

attribute [local irreducible] parametersGraph translateGraph ActualArithmeticGraph.graph conditionalBiGraph
noncomputable def renameFormulaGraph : 𝚺ᴬ₁.Semisentence 11 := .mkSigma
  “forward backward p x y b bb f ff lo z. ∃ param target a aa e,
    !parametersGraph param b f lo z ∧ !parametersGraph target bb ff lo z ∧
    !translateGraph a param p ∧ !translateGraph aa target p ∧
    !(ActualArithmeticGraph.graph neighborhoodExpr) e x y z 0 ∧
    !conditionalBiGraph forward backward e a aa”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem renameFormula_graph (forward backward p x y b bb f ff lo z : V) :
    renameFormulaGraph.val.Evalb ![forward,backward,p,x,y,b,bb,f,ff,lo,z] ↔
      ConditionalBiCertificates forward backward (neighborhoodValue x y z)
        (translate (parameters b f lo z) p) (translate (parameters bb ff lo z) p) := by
  simp [renameFormulaGraph,parameters_graph,translate_graph,ActualArithmeticGraph.graph_correct,
    conditionalBi_graph,neighborhoodValue,Matrix.comp_vecCons'']

attribute [local irreducible] renameFormulaGraph renameEnvironmentGraph coverageGraph
noncomputable def renameFormulaInvariant : ArithmeticSemisentence 1 :=
  “n. ∀ p<n, ∀ x y b bb f ff lo z, !coverageGraph b f lo z p →
    !renameEnvironmentGraph x y b bb → !renameEnvironmentGraph x y f ff → x<lo → y<lo →
    ∃ forward backward, !renameFormulaGraph forward backward p x y b bb f ff lo z”

theorem renameFormula_invariant (n : V) : renameFormulaInvariant.Evalb ![n] ↔
    ∀ p<n, ∀ x y b bb f ff lo z : V, FormulaCovered b f lo z p →
      RenameEnvironment x y b bb → RenameEnvironment x y f ff → x<lo → y<lo →
      ∃ forward backward, ConditionalBiCertificates forward backward (neighborhoodValue x y z)
        (translate (parameters b f lo z) p) (translate (parameters bb ff lo z) p) := by
  simp [renameFormulaInvariant,coverage_graph,renameEnvironment_graph,
    renameFormula_graph,Matrix.comp_vecCons'']

variable [V↓[ℒₒᵣ] ⊧* theory]

theorem rename_atom_certificates (x y b bb f ff lo z k r ts : V)
    (hb : RenameEnvironment x y b bb) (hf : RenameEnvironment x y f ff)
    (hy : z≠y) (hat : ∃ out, AtomTranslation out k r ts b f lo z) :
    ∃ forward backward, ConditionalBiCertificates forward backward (neighborhoodValue x y z)
      (totalAtom (parameters b f lo z) k r ts) (totalAtom (parameters bb ff lo z) k r ts) := by
  obtain ⟨out,hat⟩ := hat
  have hout := totalAtom_agrees hat
  obtain ⟨hk,hlen,henv,a,d,ha,hd,hhead⟩ := hat
  have hnew : totalAtom (parameters bb ff lo z) k r ts=
      totalHead r (renameLabelValue x y a) (renameLabelValue x y d) z := by
    simp only [totalAtom,parameters_bound,parameters_free,parameters_reserve]
    rw [← totalLabel_agrees (variableLabel_rename hb hf ha),
      ← totalLabel_agrees (variableLabel_rename hb hf hd)]
  rw [← hout,hnew]
  rcases hhead with ⟨rfl,he⟩ | ⟨rfl,he⟩
  · rw [he]
    simp only [totalHead,ite_true]
    exact ⟨_,_,(renameNeighborhood z x y a d).accepted⟩
  · rw [he]
    have hv : ∀ a d : V, ActualArithmeticGraph.eval membershipExpr a d z 0=wel d a := by
      intro a d
      simp [membershipExpr,wel,wim,implicationValue,ActualHeadGraphs.implicationExpr,
        ActualHeadGraphs.im,ActualHeadGraphs.mem,ActualArithmeticGraph.eval]
    simp only [totalHead,Arithmetic.one_ne_zero,ite_false,ite_true]
    rw [hv,hv]
    exact ⟨_,_,(renameMembership z x y d a (Ne.symm (label_reserved hd henv))
      (Ne.symm (label_reserved ha henv)) hy).accepted⟩

#print axioms renameFormula_graph
#print axioms renameFormula_invariant
#print axioms rename_atom_certificates
end M6.PA.RelationalSource.Numeric

