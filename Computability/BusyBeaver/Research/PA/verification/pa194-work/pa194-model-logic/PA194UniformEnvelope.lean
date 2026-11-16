import PA194UniformFullyClosedModel
import PA194UncloseTrace
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194BindSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def pureUncloseConstruction : PR.Construction V uncloseBlueprint where
  zero p := p 0
  succ _ _ previous := free SourceL (pi₂ (previous-1))
  zero_defined := .mk fun e => by simp [uncloseBlueprint,sourceQVecZeroDef]
  succ_defined := .mk fun e => by
    rcases zero_or_succ (e 1) with h | ⟨a,h⟩
    · simp [uncloseBlueprint,uncloseStepDef,pi₂,h]
    · simp [uncloseBlueprint,uncloseStepDef,pi₂,h]

theorem pureUncloseHistory_existsUnique (n p : V) :
    ∃! s : V, (pureUncloseConstruction (V := V)).CSeq ![p] s ∧ n+1 = lh s := by
  obtain ⟨s,hs,hl⟩ := PR.Construction.CSeq.exists (pureUncloseConstruction (V := V)) ![p] n
  refine ⟨s,⟨hs,hl⟩,?_⟩
  intro t ⟨ht,htl⟩
  have hlen : lh t = lh s := htl.symm.trans hl
  apply ht.seq.lh_ext hs.seq hlen
  intro i x y hx hy
  exact ht.unique hs (by rw [hlen]) (ht.seq.lt_lh_of_mem hx) hx hy

noncomputable def pureUncloseHistory (n p : V) : V := Classical.choose! (pureUncloseHistory_existsUnique n p)

theorem pureUncloseHistory_spec (n p : V) :
    (pureUncloseConstruction (V := V)).CSeq ![p] (pureUncloseHistory n p) ∧ n+1 = lh (pureUncloseHistory n p) :=
  Classical.choose!_spec (pureUncloseHistory_existsUnique n p)

theorem pureUncloseHistoryGraph_iff (s n p : V) :
    uncloseHistoryGraph.val.Eval ![s,n,p] Empty.elim ↔ s = pureUncloseHistory n p := by
  have hu := pureUncloseHistory_existsUnique n p
  have hs := pureUncloseHistory_spec n p
  have hgraph : uncloseHistoryGraph.val.Eval ![s,n,p] Empty.elim ↔
      (pureUncloseConstruction (V := V)).CSeq ![p] s ∧ n+1 = lh s := by
    simp [uncloseHistoryGraph, (pureUncloseConstruction (V := V)).cseq_defined_iff, eq_comm, Matrix.constant_eq_singleton]
  rw [hgraph]
  constructor
  · intro h
    exact hu.unique h hs
  · rintro rfl
    exact hs


local instance pureUncloseHistory_defined :
    𝚺₁-Function₂ (pureUncloseHistory : V → V → V) via uncloseHistoryGraph := .mk fun v ↦ by
  change uncloseHistoryGraph.val.Eval v Empty.elim ↔ v 0 = pureUncloseHistory (v 1) (v 2)
  have hv : ![v 0,v 1,v 2] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
        rfl
  simpa only [hv] using (pureUncloseHistoryGraph_iff (v 0) (v 1) (v 2))

noncomputable def pureWitnessEnvelope (q : V) : V := pureUncloseHistory q q
noncomputable def pureWitnessEnvelopeGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “b q. !uncloseHistoryGraph b q q”
theorem pureWitnessEnvelope_defined :
    𝚺₁-Function₁ (pureWitnessEnvelope : V → V) via pureWitnessEnvelopeGraph := .mk fun v => by
  simp [pureWitnessEnvelopeGraph,pureWitnessEnvelope]
#print axioms pureWitnessEnvelope_defined
end generic
end PA194BindSource
