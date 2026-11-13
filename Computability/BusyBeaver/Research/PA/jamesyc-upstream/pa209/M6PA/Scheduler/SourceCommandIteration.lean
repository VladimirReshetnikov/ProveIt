module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.SourceCommandResidualGraph
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.SourceCommandEncodingInternal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCommandStepGraph ActualCommandWordGraph ActualWordEncodingBlueprint

noncomputable def traversalState {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (tail initial : V) : V := tail ∷ initial ∷ 0
noncomputable def traversalStateGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “z tail initial. ∃ x, !adjoinDef x initial 0 ∧ !adjoinDef z tail x”
noncomputable def consumeStepGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “z state. ∃ tail initial, !nthDef tail state 0 ∧ !nthDef initial state 1 ∧
    ((tail=0 ∧ z=state) ∨ (tail≠0 ∧ ∃ raw atom next result,
      !subDef raw tail 1 ∧ !commandAtomGraph atom raw ∧ !residualGraph next raw ∧
      !stepGraph result atom initial ∧ !traversalStateGraph z next result))”
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def consumeStep (state : V) : V :=
  if nth state 0=0 then state else
    traversalState (residual (nth state 0-1))
      (stepValue (commandAtom (nth state 0-1)) (nth state 1))
theorem traversalState_graph (z tail initial : V) :
    traversalStateGraph.val.Evalb ![z,tail,initial] ↔ z=traversalState tail initial := by
  simp [traversalStateGraph,traversalState]
theorem consumeStep_graph (z state : V) :
    consumeStepGraph.val.Evalb ![z,state] ↔ z=consumeStep state := by
  by_cases h : nth state 0=0 <;>
    simp [consumeStepGraph,commandAtom_graph,residual_graph,step_graph,traversalState_graph,consumeStep,h]

noncomputable def iterationBlueprint : PR.Blueprint 1 where
  zero := .mkSigma “z initial. z=initial”
  succ := consumeStepGraph.rew (Rew.subst ![#0,#1])
noncomputable def iterationConstruction : PR.Construction V iterationBlueprint where
  zero := fun p => p 0
  succ := fun _ _ state => consumeStep state
  zero_defined := .mk fun v => by simp [iterationBlueprint]
  succ_defined := .mk fun v => by simp [iterationBlueprint,consumeStep_graph]
noncomputable def consume (n initial : V) : V := iterationConstruction.result ![initial] n
noncomputable def consumeGraph : 𝚺ᴬ₁.Semisentence 3 := iterationBlueprint.resultDef
@[simp] theorem consume_zero (state : V) : consume 0 state=state := by simp [consume,iterationConstruction]
@[simp] theorem consume_succ (n state : V) : consume (n+1) state=consumeStep (consume n state) := by
  simp [consume,iterationConstruction]
theorem consume_graph (z n state : V) : consumeGraph.val.Evalb ![z,n,state] ↔ z=consume n state := by
  simpa [consumeGraph,consume,Matrix.constant_eq_singleton] using
    (iterationConstruction (V:=V)).result_defined_iff ![z,n,state]


instance consume_defined : 𝚺ᴬ₁-Function₂ (consume : V→V→V) via consumeGraph := .mk fun v => by
  have hv : v=![v 0,v 1,v 2] := by
    funext ⟨i,hi⟩
    have he : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases he with rfl|rfl|rfl <;> rfl
  rw [hv]; exact consume_graph _ _ _
instance consume_sigma : 𝚺ᴬ₁-Function₂ (consume : V→V→V) := consume_defined.to_definable
instance consume_definable (Γ m) : Γᴬ_[m+1]-Function₂ (consume : V→V→V) :=
  consume_sigma.of_sigmaOne
instance consumeStep_defined : 𝚺ᴬ₁-Function₁ (consumeStep : V→V) via consumeStepGraph := .mk fun v => by
  have hv : v=![v 0,v 1] := by
    funext ⟨i,hi⟩
    have he : i=0 ∨ i=1 := by omega
    rcases he with rfl|rfl <;> rfl
  rw [hv]; exact consumeStep_graph _ _
instance consumeStep_sigma : 𝚺ᴬ₁-Function₁ (consumeStep : V→V) := consumeStep_defined.to_definable
instance consumeStep_definable (Γ m) : Γᴬ_[m+1]-Function₁ (consumeStep : V→V) :=
  consumeStep_sigma.of_sigmaOne

theorem consume_succ_start (n initial : V) :
    consume (n+1) initial=consume n (consumeStep initial) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa only [zero_add,consume_zero] using consume_succ (0:V) initial
  case succ n ih => rw [consume_succ,ih,consume_succ]

theorem consume_encoded_step (atom xs initial : V) :
    consumeStep (traversalState (encodeValue (atom∷xs)) initial)=
      traversalState (encodeValue xs) (stepValue atom initial) := by
  have hn : spliceValue atom (encodeValue xs)+1≠0 := by simp
  have hidx (x xs : V) : nth (x∷xs) 1=nth xs 0 := by
    simpa only [zero_add] using nth_adjoin_succ x xs 0
  simp only [encode_adjoin,consumeStep,traversalState,nth_adjoin_zero,hidx,
    hn,ite_false,add_sub_self,splice_residual,splice_atom,commandAtom_step]

#print axioms consume_succ_start
#print axioms consume_encoded_step
#print axioms consume_graph
#print axioms consumeStep_graph
end M6.PA.SourceCommandEncodingInternal

