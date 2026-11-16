module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.SourceCommandIteration
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.SourceCommandEncodingInternal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCommandStepGraph ActualCommandWordGraph ActualWordEncodingBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local instance encode_sigma : 𝚺ᴬ₁-Function₁ (encodeValue : V→V) := encode_defined.to_definable
local instance encode_hierarchy (Γ m) : Γᴬ_[m+1]-Function₁ (encodeValue : V→V) := encode_sigma.of_sigmaOne
local instance word_hierarchy (Γ m) : Γᴬ_[m+1]-Function₂ (wordValue : V→V→V) := word_definable.of_sigmaOne

/-- Consume the exact encoded source tail for every HFS word, including words
of nonstandard length. Arbitrary standalone atom tails are normalized with
proved step invariance; the source stack is not identified with the HFS word. -/
theorem consume_encoded_word (xs initial : V) :
    consume (len xs) (traversalState (encodeValue xs) initial)=
      traversalState 0 (wordValue xs initial) := by
  induction xs using adjoin_ISigma1.pi1_succ_induction generalizing initial
  · unfold traversalState
    definability
  case nil => simp
  case adjoin atom xs ih =>
    rw [len_adjoin,consume_succ_start,consume_encoded_step,ih,word_cons]

#print axioms consume_encoded_word
end M6.PA.SourceCommandEncodingInternal

