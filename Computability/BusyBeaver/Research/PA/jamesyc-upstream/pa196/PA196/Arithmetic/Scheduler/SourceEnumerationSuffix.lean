module
public import PA196.Arithmetic.Scheduler.Base
public import PA196.Program
public import PA196.Source.Readers
public import PA196.Arithmetic.Scheduler.InternalCodedSourceCandidate
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 M6.PA PA196.Arithmetic PA196.Arithmetic.Scheduler
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Scheduler.SourceCommandEncodingInternal
open PA196.Arithmetic.Scheduler.ActualCandidateBlueprint PA196.Arithmetic.Scheduler.ActualWordEncodingBlueprint
open M6.PA.SourceCantorInternal PA196.Arithmetic.CommandStep

/-- Enumerate a suffix beginning at an arbitrary model-valued candidate. -/
noncomputable def fromBlueprint : PR.Blueprint 2 where
  zero := .mkSigma “z base initial. z=initial”
  succ := candidateRunGraph.rew (Rew.subst ![#0,‘#3+#2’,#1])
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* PA196.Arithmetic.Machine.PA.theory]
noncomputable def fromConstruction : PR.Construction V fromBlueprint where
  zero := fun p => p 1
  succ := fun p n state => candidateRun (p 0+n) state
  zero_defined := .mk fun v => by simp [fromBlueprint]
  succ_defined := .mk fun v => by simp [fromBlueprint,candidateRun_graph]
noncomputable def fromValue (base n initial : V) : V := fromConstruction.result ![base,initial] n
noncomputable def fromGraph : 𝚺ᴬ₁.Semisentence 4 := fromBlueprint.resultDef
@[simp] theorem from_zero (base initial : V) : fromValue base 0 initial=initial := by
  simp [fromValue,fromConstruction]
@[simp] theorem from_succ (base n initial : V) :
    fromValue base (n+1) initial=candidateRun (base+n) (fromValue base n initial) := by
  simp [fromValue,fromConstruction]
theorem from_graph (z n base initial : V) :
    fromGraph.val.Evalb ![z,n,base,initial] ↔ z=fromValue base n initial := by
  simpa [fromGraph,fromValue] using
    (fromConstruction (V := V)).result_defined_iff ![z,n,base,initial]

end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
