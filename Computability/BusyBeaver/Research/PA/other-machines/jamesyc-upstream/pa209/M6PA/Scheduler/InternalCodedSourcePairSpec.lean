module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceExt
public import M6PA.Scheduler.InternalCodedSourceDrainTwo
public import M6PA.Scheduler.SourceCantorInternal
public import M6.Source.AXPair
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

noncomputable def pairLoopEndGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “z n xs. ∃ a t ys, !nthDef a xs 7 ∧ !SourceCantorInternal.triangleGraph t n ∧
    !(replaceGraph 6) ys xs 0 ∧ !(replaceGraph 7) z ys (a+t)”
noncomputable def pairLoopFormula (offset : Nat) : ArithmeticSemisentence 1 :=
  “n. ∀ xs, (!lenDef 9 xs ∧ !nthDef 0 xs 1 ∧ !nthDef n xs 6) →
    ∃ ys a b k cs, !pairLoopEndGraph ys n xs ∧
      !adjoinDef a ↑(offset+36) xs ∧ !adjoinDef b ↑(offset+42) ys ∧
      0<k ∧ !traceGraph k cs a b”
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def pairLoopEnd (n xs : V) : V :=
  replace 7 (replace 6 xs 0) (registers xs 7+SourceCantorInternal.triangleValue n)
theorem pairLoopEnd_graph (z n xs : V) :
    pairLoopEndGraph.val.Evalb ![z,n,xs] ↔ z=pairLoopEnd n xs := by
  simp [pairLoopEndGraph,SourceCantorInternal.triangle_graph,
    (replace_defined 6).df,(replace_defined 7).df,pairLoopEnd,registers,numeral_eq_natCast,Nat.cast_ofNat]
theorem pairLoop_formula (offset : Nat) (n : V) :
    (pairLoopFormula offset).Evalb ![n] ↔
      ∀ xs : V, ValidStore xs → registers xs 1=0 → registers xs 6=n → ∃ k cs,
        0<k ∧ Trace k cs (stateCode ((offset+36:Nat):V) xs)
          (stateCode ((offset+42:Nat):V) (pairLoopEnd n xs)) := by
  simp [pairLoopFormula,pairLoopEnd_graph,trace_correct,ValidStore,registers,stateCode,
    numeral_eq_natCast,Nat.cast_ofNat,eq_comm,Matrix.comp_vecCons'']
#print axioms pairLoop_formula
end M6.Arithmetic.PA.InternalTrace.CodedSource

