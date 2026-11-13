module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.SourceCantorDecodeInternal
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.SourceCantorInternal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance triangleValue_defined : 𝚺ᴬ₁-Function₁[V] triangleValue via triangleGraph := .mk fun v => by
  have hv : v = ![v 0,v 1] := by
    funext ⟨i,hi⟩
    have he : i=0 ∨ i=1 := by omega
    rcases he with rfl | rfl <;> rfl
  rw [hv]
  exact triangle_graph _ _
instance triangleValue_definable : 𝚺ᴬ₁-Function₁[V] triangleValue := triangleValue_defined.to_definable
instance pairValue_definable : 𝚺ᴬ₁-Function₂[V] pairValue := by
  unfold pairValue
  definability
instance decodeState_defined : 𝚺ᴬ₁-Function₁[V] decodeState via decodeStateGraph := .mk fun v => by
  have hv : v = ![v 0,v 1] := by
    funext ⟨i,hi⟩
    have he : i=0 ∨ i=1 := by omega
    rcases he with rfl | rfl <;> rfl
  rw [hv]
  exact decodeState_graph _ _
instance decodeState_definable : 𝚺ᴬ₁-Function₁[V] decodeState := decodeState_defined.to_definable
instance decodeLeft_definable : 𝚺ᴬ₁-Function₁[V] decodeLeft := by
  unfold decodeLeft
  definability
instance decodeRight_definable : 𝚺ᴬ₁-Function₁[V] decodeRight := by
  unfold decodeRight
  definability

theorem pairValue_advance (a b : V) :
    pairValue (π₁ (advanceState ⟪a,b⟫)) (π₂ (advanceState ⟪a,b⟫)) = pairValue a b+1 := by
  rcases zero_or_succ a with rfl | ⟨a,rfl⟩
  · simp [advanceState,pairValue,triangle_succ,add_assoc]
  · simp [advanceState,pairValue,add_assoc,add_comm,add_left_comm]

theorem pairValue_advanceState (z : V) :
    pairValue (π₁ (advanceState z)) (π₂ (advanceState z)) = pairValue (π₁ z) (π₂ z)+1 := by
  simpa only [pair_unpair] using pairValue_advance (π₁ z) (π₂ z)

/-- Uniform inverse direction for every element of every IΣ1 model, not only
standard numerals. Its induction predicate uses the explicit graph instances. -/
theorem pairValue_decode (n : V) : pairValue (decodeLeft n) (decodeRight n) = n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp [decodeLeft,decodeRight,pairValue]
  case succ n ih =>
    change pairValue (π₁ (decodeState (n+1))) (π₂ (decodeState (n+1))) = n+1
    rw [decodeState_succ,pairValue_advanceState]
    exact congrArg (fun x : V => x+1) ih

noncomputable def decodeInverseSentence : ArithmeticSentence :=
  “∀ n a b, !decodeGraph a b n → !pairGraph n a b”

theorem pa_proves_decode_inverse : theory ⊢ decodeInverseSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [decodeInverseSentence,models_iff]
  simp [decode_graph,pair_graph,pairValue_decode]

#print axioms pairValue_decode
#print axioms pa_proves_decode_inverse
end M6.PA.SourceCantorInternal

