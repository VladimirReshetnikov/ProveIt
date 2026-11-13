module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.SourceCommandEnumeration
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.SourceCommandEncodingInternal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCommandStepGraph
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local instance residual_termination_sigma : 𝚺ᴬ₁-Function₁ (residual : V→V) := residual_defined.to_definable
local instance residual_termination_hierarchy (Γ m) : Γᴬ_[m+1]-Function₁ (residual : V→V) := residual_termination_sigma.of_sigmaOne

theorem consume_positive_step (raw initial : V) :
    consumeStep (traversalState (raw+1) initial)=
      traversalState (residual raw) (stepValue (commandAtom raw) initial) := by
  have h1 (x xs : V) : nth (x∷xs) 1=nth xs 0 := by
    simpa only [zero_add] using nth_adjoin_succ x xs 0
  simp [consumeStep,traversalState,h1]

/-- Every source residual, including malformed command data, finishes within
its own model-valued numeric bound. Zero residual remains stable. -/
theorem consume_finishes (n tail initial : V) (ht : tail≤n) :
    nth (consume n (traversalState tail initial)) 0=0 := by
  induction n using ISigma1.pi1_succ_induction generalizing tail initial
  · unfold traversalState
    definability
  case zero =>
    have hz : tail=0 := by simpa using ht
    simp [hz,traversalState]
  case succ n ih =>
    rcases zero_or_succ tail with rfl | ⟨raw,rfl⟩
    · rw [consume_empty]
      simp [traversalState]
    · rw [consume_succ_start,consume_positive_step]
      have hr : raw≤n := (add_le_add_iff_right 1).mp ht
      exact ih _ _ (le_trans (residual_le raw) hr)

theorem every_candidate_finished (n initial : V) :
    nth (consume (n+1) (traversalState (n+1) initial)) 0=0 :=
  consume_finishes _ _ _ (le_refl _)

@[simp] theorem traversal_first (tail initial : V) : nth (traversalState tail initial) 0=tail := by
  simp [traversalState]
@[simp] theorem traversal_second (tail initial : V) : nth (traversalState tail initial) 1=initial := by
  have h1 (x xs : V) : nth (x∷xs) 1=nth xs 0 := by
    simpa only [zero_add] using nth_adjoin_succ x xs 0
  simp [traversalState,h1]

theorem consumeStep_shape (tail initial : V) :
    consumeStep (traversalState tail initial)=
      traversalState (nth (consumeStep (traversalState tail initial)) 0)
        (nth (consumeStep (traversalState tail initial)) 1) := by
  rcases zero_or_succ tail with rfl | ⟨raw,rfl⟩
  · simp [consumeStep]
  · rw [consume_positive_step]
    simp

theorem consume_shape (n tail initial : V) :
    consume n (traversalState tail initial)=
      traversalState (nth (consume n (traversalState tail initial)) 0)
        (nth (consume n (traversalState tail initial)) 1) := by
  induction n using ISigma1.sigma1_succ_induction
  · unfold traversalState; definability
  case zero => simp
  case succ n ih =>
    rw [consume_succ]
    generalize he : consume n (traversalState tail initial)=state at ih ⊢
    rw [ih]
    exact consumeStep_shape _ _

theorem every_candidate_result (n initial : V) :
    consume (n+1) (traversalState (n+1) initial)=traversalState 0 (candidateRun n initial) := by
  rw [consume_shape,every_candidate_finished]
  rfl

theorem consume_halted (n tail : V) : nth (consume n (traversalState tail 0)) 1=0 := by
  induction n using ISigma1.pi1_succ_induction generalizing tail
  · unfold traversalState; definability
  case zero => simp
  case succ n ih =>
    rcases zero_or_succ tail with rfl | ⟨raw,rfl⟩
    · rw [consume_empty]; simp
    · rw [consume_succ_start,consume_positive_step,step_halted]
      exact ih _

theorem candidateRun_halted (n : V) : candidateRun n 0=0 := consume_halted _ _
#print axioms every_candidate_result
#print axioms candidateRun_halted
#print axioms consume_finishes
#print axioms every_candidate_finished
end M6.PA.SourceCommandEncodingInternal

