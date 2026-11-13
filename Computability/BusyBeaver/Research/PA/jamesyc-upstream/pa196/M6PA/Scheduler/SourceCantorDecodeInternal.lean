module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.SourceCantorInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.SourceCantorInternal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

/-- Foundation pairing here stores the two coordinates of the recursion state;
it is not identified with the source Cantor pair being decoded. -/
noncomputable def decodeBlueprint : PR.Blueprint 0 where
  zero := .mkSigma “z. !pairDef z 0 0”
  succ := .mkSigma “u z i. ∃ a b, !pi₁Def a z ∧ !pi₂Def b z ∧
    ((a = 0 ∧ !pairDef u (b+1) 0) ∨
     (a ≠ 0 ∧ ∃ p, !subDef p a 1 ∧ !pairDef u p (b+1)))”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def advanceState (z : V) : V :=
  if π₁ z = 0 then ⟪π₂ z+1,0⟫ else ⟪π₁ z-1,π₂ z+1⟫

noncomputable def decodeConstruction : PR.Construction V decodeBlueprint where
  zero := fun _ => ⟪0,0⟫
  succ := fun _ _ z => advanceState z
  zero_defined := .mk fun v => by simp [decodeBlueprint]
  succ_defined := .mk fun v => by
    by_cases h : π₁ (v 1) = 0 <;> simp [decodeBlueprint,advanceState,h]

noncomputable def decodeState (n : V) : V := decodeConstruction.result ![] n
noncomputable def decodeStateGraph : 𝚺ᴬ₁.Semisentence 2 := decodeBlueprint.resultDef

@[simp] theorem decodeState_zero : decodeState (0 : V) = ⟪0,0⟫ := by
  simp [decodeState,decodeConstruction]
@[simp] theorem decodeState_succ (n : V) : decodeState (n+1) = advanceState (decodeState n) := by
  simp [decodeState,decodeConstruction]

theorem decodeState_graph (z n : V) : decodeStateGraph.val.Evalb ![z,n] ↔ z=decodeState n := by
  have he : (fun _ : Fin 0 => n) = (![] : Fin 0 → V) := by
    funext i
    exact Fin.elim0 i
  simpa [decodeStateGraph,decodeState,he] using
    (decodeConstruction (V := V)).result_defined_iff ![z,n]

theorem decodeState_standard (n : Nat) :
    decodeState n = ⟪(M6.Source.Cantor.decode n).1,(M6.Source.Cantor.decode n).2⟫ := by
  induction n with
  | zero => simp [M6.Source.Cantor.decode]
  | succ n ih =>
      rw [decodeState_succ,ih,M6.Source.Cantor.decode]
      rcases h : M6.Source.Cantor.decode n with ⟨a,b⟩
      cases a <;> simp [advanceState,M6.Source.Cantor.advance]

noncomputable def decodeLeft (n : V) : V := π₁ (decodeState n)
noncomputable def decodeRight (n : V) : V := π₂ (decodeState n)
noncomputable def decodeGraph : 𝚺ᴬ₁.Semisentence 3 :=
  .mkSigma “a b n. ∃ z, !decodeStateGraph z n ∧ !pi₁Def a z ∧ !pi₂Def b z”

theorem decode_graph (a b n : V) :
    decodeGraph.val.Evalb ![a,b,n] ↔ a=decodeLeft n ∧ b=decodeRight n := by
  simp [decodeGraph,decodeState_graph,decodeLeft,decodeRight]

theorem decode_standard (n : Nat) :
    (decodeLeft n,decodeRight n) = M6.Source.Cantor.decode n := by
  simp [decodeLeft,decodeRight,decodeState_standard]

noncomputable def decodeTotalSentence : ArithmeticSentence := “∀ n, ∃ a b, !decodeGraph a b n”
theorem pa_proves_decode_total : theory ⊢ decodeTotalSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [decodeTotalSentence,models_iff]
  simp [decode_graph]

#print axioms decodeState_standard
#print axioms decode_standard
#print axioms pa_proves_decode_total
end M6.PA.SourceCantorInternal

