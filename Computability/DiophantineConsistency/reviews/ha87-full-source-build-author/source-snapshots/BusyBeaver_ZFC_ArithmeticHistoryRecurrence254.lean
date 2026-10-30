import BusyBeaver.ZFC.ArithmeticHistory254

/-!
Internal recurrence laws for the unchanged twelve-rule proof evaluator.
All indices may be nonstandard elements of an IΣ1 model. These are laws for
that evaluator, not an internal proof compiler or execution theorem.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticHistoryRecurrence254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticRow254 ArithmeticHistory254
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance value_definable : 𝚺₁-Function₁[V] value := value_defined.to_definable

/-- Every earlier entry is the value at its own index, internally. -/
theorem history_lookup_le (code : V) :
    ∀ i ≤ code, znth (history code) i = value i := by
  induction code using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro i hi
    have hi0 : i = 0 := le_antisymm hi (by simp)
    subst i
    rfl
  case succ code ih =>
    intro i hi
    by_cases he : i = code + 1
    · subst i
      rfl
    · have hilt : i < code + 1 := lt_of_le_of_ne hi he
      have hile : i ≤ code := lt_succ_iff_le.mp hilt
      rw [history_succ, znth_append_old (history_seq code) _ i
        (by simpa only [history_length] using hilt)]
      exact ih i hile

/-- The exterior default is exactly zero, at all internal indices. -/
theorem history_lookup (code i : V) :
    znth (history code) i = if i ≤ code then value i else 0 := by
  classical
  by_cases hi : i ≤ code
  · simp only [hi, if_pos]
    exact history_lookup_le code i hi
  · simp only [hi, if_false]
    apply znth_prop_not
    right
    rw [history_length]
    exact lt_iff_succ_le.mp (lt_of_not_ge hi)

/-- Positive proof code raw+1 selects payload raw/12. -/
theorem quotient_le (raw : V) : raw / 12 ≤ raw := Arithmetic.div_le raw 12

theorem tail_le (raw : V) : second (raw / 12) ≤ raw :=
  le_trans (projections_spec (raw / 12)).2.1 (quotient_le raw)

theorem minor_le (raw : V) : first (second (raw / 12)) ≤ raw :=
  le_trans (projections_spec (second (raw / 12))).1 (tail_le raw)

theorem major_le (raw : V) : second (second (raw / 12)) ≤ raw :=
  le_trans (projections_spec (second (raw / 12))).2.1 (tail_le raw)

/-- First expose the exact stored successor entry. -/
theorem value_succ_step (raw : V) :
    value (raw + 1) = positiveStep (history raw) raw := by
  unfold value
  rw [history_succ]
  simpa only [history_length, stepValue_succ] using
    znth_append_last (history_seq raw) (stepValue (history raw) (raw + 1))

/-- The actual row now receives child VALUES, not sequence lookups. -/
theorem value_succ (raw : V) :
    value (raw + 1) = rowKernel (raw % 12) (raw / 12)
      (if raw % 12 = 2 then value (second (raw / 12))
       else value (first (second (raw / 12))))
      (value (second (second (raw / 12)))) := by
  rw [value_succ_step]
  unfold positiveStep
  dsimp only
  rw [history_lookup_le raw _ (tail_le raw),
      history_lookup_le raw _ (minor_le raw),
      history_lookup_le raw _ (major_le raw)]

/-- Accepted MP keeps the original bounded predecessor/implication gate. -/
theorem mp_parent_gate (raw : V) (htag : raw % 12 = 1)
    (hvalid : value (raw + 1) ≠ 0) :
    MPGate (first (raw / 12))
      (value (first (second (raw / 12))))
      (value (second (second (raw / 12)))) := by
  classical
  by_contra hgate
  apply hvalid
  rw [value_succ]
  simp [rowKernel, htag, mpValue, hgate]

/-- A valid MP parent forces validity of BOTH actual child codes. -/
theorem mp_parent_children (raw : V) (htag : raw % 12 = 1)
    (hvalid : value (raw + 1) ≠ 0) :
    value (first (second (raw / 12))) ≠ 0 ∧
      value (second (second (raw / 12))) ≠ 0 := by
  rcases mp_parent_gate raw htag hvalid with ⟨x, _, m, _, hu, hv, _⟩
  constructor
  · rw [hu]
    simp
  · rw [hv]
    simp

/-- A valid GEN parent forces validity of its WHOLE-tail child code. -/
theorem gen_parent_child (raw : V) (htag : raw % 12 = 2)
    (hvalid : value (raw + 1) ≠ 0) :
    value (second (raw / 12)) ≠ 0 := by
  intro hchild
  apply hvalid
  rw [value_succ]
  simp [rowKernel, htag, genValue, hchild]

end SetTheory.BusyBeaver.ZFC.ArithmeticHistoryRecurrence254
