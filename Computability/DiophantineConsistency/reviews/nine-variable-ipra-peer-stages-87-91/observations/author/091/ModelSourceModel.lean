import DiophantineConsistency.ModelSyntaxPipeline
import DiophantineConsistency.ModelOptimizer
import DiophantineConsistency.ModelRepBasic
import DiophantineConsistency.IPRAExplicitZFCReduction

/-! # `SourceModel` from the compiler, the optimizer and the program link

`IPRAExplicitZFCReduction.SourceModel` says that, in every model `V` of
`𝗜𝚺₁`, the compacted source equation has a solution iff the internal C222
enumerator halts from `⟨0,4,0,…⟩`. It factors into three internal steps:

1. syntax (`ModelSyntaxPipeline.compacted_iff_internalZero`): the compacted,
   simplified equation is solvable in `V` iff `source.expression` has an
   internal zero;
2. compilation (`source_iff`): by `ModelRepBasic.existsValue_holds` (given
   the primitive-recursion case `PrecCase`) and the internal optimizer
   correctness `ModelOptimizer.evalV_optimize`, that happens iff some
   internal input makes the *unoptimized* literal enumerator program
   `DirectEnumerator.program` output `1`;
3. the program link `ProgramLink`: the internal semantics of
   `DirectEnumerator.program` reaches `1` iff the internal machine
   `ArithmeticEnumRunPerm222.run` halts from `liveValue 0 4 0`.

`sourceModel_of_link` assembles them. Step 3 is stated here as the explicit
proposition `ProgramLink`; it is not assumed anywhere as an axiom. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelSourceModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelRep ModelRepBasic ModelScalarPR

/-- The compiled graph of a supplied program is internally correct for the
internal semantics of its code; the specification layer changes no syntax. -/
theorem graphHolds_realizes (hprec : PrecCase) {f : ℕ → ℕ} (p : ScalarPRCode.Realizes f) :
    GraphHolds p.graphRep (evalFun p.val) :=
  graphRep_holds hprec p.val

/-- Existential acceptance for a supplied program, internally. -/
theorem existsValue_realizes_holds (hprec : PrecCase) {f : ℕ → ℕ}
    (p : ScalarPRCode.Realizes f) (accepted : ℕ) :
    Holds (GraphRep.existsValue p.graphRep accepted)
      (fun V _ _ _ => ∃ t : V, evalV p.val t = (accepted : V)) :=
  holds_existsValue (graphHolds_realizes hprec p) accepted

/-- The optimized program used by `ExplicitZFCSyntax` has the internal
semantics of the literal enumerator program. -/
theorem evalV_program {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (t : V) :
    evalV ExplicitZFCSyntax.program.val t = evalV DirectEnumerator.program.val t := by
  unfold ExplicitZFCSyntax.program
  exact ModelOptimizer.evalV_realizes_optimize DirectEnumerator.program t

/-- Step 2: an internal zero of the source expression is an internal input on
which the literal enumerator program outputs `1`. -/
theorem source_iff (hprec : PrecCase) (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    (∃ w : Fin IPRAExplicitZFCReduction.source.witnessCount → V,
      AdaptiveEquationSyntax2011.InternalZero IPRAExplicitZFCReduction.source.expression
        (Sum.elim Empty.elim w)) ↔
      ∃ t : V, evalV DirectEnumerator.program.val t = 1 := by
  have h := existsValue_realizes_holds hprec ExplicitZFCSyntax.program 1 V
    (Empty.elim : Empty → V)
  refine h.symm.trans (exists_congr fun t => ?_)
  rw [Nat.cast_one, evalV_program]

/-- Step 3, the program link: inside every model of `𝗜𝚺₁`, the literal
enumerator program outputs `1` at some input iff the internal C222 machine
halts from the literal initial state `⟨0,4,0,0,0,0⟩`. -/
def ProgramLink : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    (∃ t : V, evalV DirectEnumerator.program.val t = 1) ↔
      ∃ time : V,
        ArithmeticEnumRunPerm222.run time (ArithmeticEnumStepPerm222.liveValue 0 4 0) = 0

/-- `SourceModel` from the primitive-recursion case and the program link. -/
theorem sourceModel_of_link (hprec : PrecCase) (hlink : ProgramLink) :
    IPRAExplicitZFCReduction.SourceModel := by
  intro V _ _
  exact (ModelSyntaxPipeline.compacted_iff_internalZero (R := V)
    IPRAExplicitZFCReduction.source).trans ((source_iff hprec V).trans (hlink V))

end DiophantineConsistency.ModelSourceModel
