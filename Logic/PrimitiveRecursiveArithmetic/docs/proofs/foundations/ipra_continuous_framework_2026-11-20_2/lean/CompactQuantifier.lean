import FiniteExtrema

/-!
# Quantifying from a finite net of scores

Theorems about finite observations of an arbitrary semantic type.  `covers`
and `evaluates` are explicitly retained mathematical hypotheses.  In a metric
application, `covers` follows from the domain net and a modulus for the
observable.  These hypotheses do not supply a compactness or choice theorem.

For an iPRA instance, functions must be fixed PR programs, universal semantic
hypotheses must be replaced by their finite used instances, and the proofs
must be reified into `Prf PRAAx`.  See ObjectTheoryPlan.lean.txt.
-/

namespace QuantitativeIPRA

universe u

structure ScoreNet (α : Type u) where
  value : α → Nat
  sample : Nat → α
  score : Nat → Nat
  last : Nat
  meshError : Nat
  evaluationError : Nat
  covers : ∀ x, ∃ i, i ≤ last ∧ Close meshError (value x) (value (sample i))
  evaluates : ∀ i, i ≤ last → Close evaluationError (score i) (value (sample i))

namespace ScoreNet

variable {α : Type u} (S : ScoreNet α)

def lower : Nat := minScore S.score S.last
def upper : Nat := maxScore S.score S.last
def minPoint : α := S.sample (argmin S.score S.last)
def maxPoint : α := S.sample (argmax S.score S.last)

/-- Every semantic value bounds the finite minimum, with mesh plus evaluation error. -/
theorem lower_le_value (x : α) :
    S.lower ≤ S.value x + (S.meshError + S.evaluationError) := by
  rcases S.covers x with ⟨i, hi, hxi⟩
  have he := S.evaluates i hi
  have hm := min_le_score S.score S.last i hi
  unfold lower
  rcases hxi with ⟨hxi₁, hxi₂⟩
  rcases he with ⟨he₁, he₂⟩
  omega

theorem value_le_upper (x : α) :
    S.value x ≤ S.upper + (S.meshError + S.evaluationError) := by
  rcases S.covers x with ⟨i, hi, hxi⟩
  have he := S.evaluates i hi
  have hm := score_le_max S.score S.last i hi
  unfold upper
  rcases hxi with ⟨hxi₁, hxi₂⟩
  rcases he with ⟨he₁, he₂⟩
  omega

/-- A genuine semantic point achieves the finite infimum up to evaluation error. -/
theorem minimum_witness : S.value S.minPoint ≤ S.lower + S.evaluationError := by
  have he := (S.evaluates _ (argmin_le S.score S.last)).2
  simpa only [minPoint, lower, argmin_attains] using he

theorem maximum_witness : S.upper ≤ S.value S.maxPoint + S.evaluationError := by
  have he := (S.evaluates _ (argmax_le S.score S.last)).1
  simpa only [maxPoint, upper, argmax_attains] using he

/-- No choice: the returned witness is the explicitly defined least argmin. -/
theorem selected_minimum (x : α) :
    S.value S.minPoint ≤ S.value x + (S.meshError + 2 * S.evaluationError) := by
  have h₁ := S.minimum_witness
  have h₂ := S.lower_le_value x
  omega

theorem selected_maximum (x : α) :
    S.value x ≤ S.value S.maxPoint + (S.meshError + 2 * S.evaluationError) := by
  have h₁ := S.maximum_witness
  have h₂ := S.value_le_upper x
  omega

variable (T : ScoreNet α)

/-- Two unrelated finite nets: one mesh error suffices in each direction. -/
theorem lower_compare (hvalue : ∀ x, S.value x = T.value x) :
    S.lower ≤ T.lower + (S.meshError + S.evaluationError + T.evaluationError) := by
  have h₁ := S.lower_le_value T.minPoint
  have h₂ := T.minimum_witness
  rw [hvalue] at h₁
  omega

theorem upper_compare (hvalue : ∀ x, S.value x = T.value x) :
    S.upper ≤ T.upper + (T.meshError + S.evaluationError + T.evaluationError) := by
  have h₁ := S.maximum_witness
  have h₂ := T.value_le_upper S.maxPoint
  rw [hvalue] at h₁
  omega

/-- Coherence uses metric coverage, not compatible finite argmin indices. -/
theorem lower_stability (hvalue : ∀ x, S.value x = T.value x) :
    Close (max S.meshError T.meshError + S.evaluationError + T.evaluationError)
      S.lower T.lower := by
  have h₁ := S.lower_compare T hvalue
  have h₂ := T.lower_compare S (fun x => (hvalue x).symm)
  constructor <;> omega

theorem upper_stability (hvalue : ∀ x, S.value x = T.value x) :
    Close (max S.meshError T.meshError + S.evaluationError + T.evaluationError)
      S.upper T.upper := by
  have h₁ := S.upper_compare T hvalue
  have h₂ := T.upper_compare S (fun x => (hvalue x).symm)
  constructor <;> omega

/-- Model comparison may be supplied as a pointwise numerical error. -/
theorem lower_compare_perturbed (e : Nat)
    (hvalue : ∀ x, Close e (S.value x) (T.value x)) :
    S.lower ≤ T.lower + (S.meshError + S.evaluationError + T.evaluationError + e) := by
  have h₁ := S.lower_le_value T.minPoint
  have h₂ := T.minimum_witness
  have h₃ := (hvalue T.minPoint).1
  omega

theorem upper_compare_perturbed (e : Nat)
    (hvalue : ∀ x, Close e (S.value x) (T.value x)) :
    S.upper ≤ T.upper + (T.meshError + S.evaluationError + T.evaluationError + e) := by
  have h₁ := S.maximum_witness
  have h₂ := T.value_le_upper S.maxPoint
  have h₃ := (hvalue S.maxPoint).1
  omega

end ScoreNet
end QuantitativeIPRA
