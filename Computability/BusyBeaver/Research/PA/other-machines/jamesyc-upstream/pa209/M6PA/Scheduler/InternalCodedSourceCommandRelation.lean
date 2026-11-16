module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalCodedSourceCommandBlocks
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

def commandStateGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “s xs. ∃ t w d h a b c, !nthDef t xs 1 ∧ !nthDef w xs 2 ∧ !nthDef d xs 4 ∧ !nthDef h xs 5 ∧
    !adjoinDef a h 0 ∧ !adjoinDef b d a ∧ !adjoinDef c w b ∧ !adjoinDef s t c”

def commandRelationGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “c n l s. (s=0 ∧ !fstIdxDef 0 c) ∨
    (∃ xs, !fstIdxDef 1 c ∧ !sndIdxDef xs c ∧ !lenDef 9 xs ∧
      !nthDef 0 xs 3 ∧ !nthDef 0 xs 6 ∧ !nthDef 0 xs 7 ∧
      !nthDef n xs 0 ∧ !nthDef l xs 8 ∧ !commandStateGraph s xs)”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
/-- Halted arithmetic execution needs only literal source halt. For live execution,
all scratch, candidate and residual fields are retained in the full HFS9 store. -/
def CommandRelation (c n l s : V) : Prop :=
  (s=0 ∧ control c=0) ∨ (control c=1 ∧ ValidStore (store c) ∧ CommandClean (store c) ∧
    registers (store c) 0=n ∧ registers (store c) 8=l ∧ commandState (store c)=s)

theorem commandState_correct (v : Fin 2 → V) :
    (V ⊧/v commandStateGraph.val) ↔ v 0=commandState (v 1) := by
  simp [commandStateGraph,commandState,ActualCommandStepGraph.stateCode,registers,
    nth_defined.df,adjoin_defined.df,numeral_eq_natCast,Nat.cast_ofNat,Nat.cast_one]

theorem commandRelation_correct (v : Fin 4 → V) :
    (V ⊧/v commandRelationGraph.val) ↔ CommandRelation (v 0) (v 1) (v 2) (v 3) := by
  simp [commandRelationGraph,CommandRelation,CommandClean,ValidStore,control,store,registers,
    commandState_correct,fstIdx_defined.df,sndIdx_defined.df,len_defined.df,nth_defined.df,
    numeral_eq_natCast,Nat.cast_ofNat,Nat.cast_one,eq_comm,and_assoc]

theorem commandRelation_root (xs : V) (hv : ValidStore xs) (hc : CommandClean xs) :
    CommandRelation (stateCode 1 xs) (registers xs 0) (registers xs 8) (commandState xs) := by
  simp [CommandRelation,control_state,store_state,hv,hc]

theorem commandRelation_halt (c n l : V) (hc : control c=0) : CommandRelation c n l 0 :=
  Or.inl ⟨rfl,hc⟩
#print axioms commandState_correct
#print axioms commandRelation_correct
#print axioms commandRelation_root
end M6.Arithmetic.PA.InternalTrace.CodedSource

