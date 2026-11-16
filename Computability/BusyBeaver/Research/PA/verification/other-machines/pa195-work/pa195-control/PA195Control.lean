import PA195ControlData
set_option autoImplicit false
set_option maxRecDepth 65536
namespace PA195LocalQuotient

/-- Every defined parent step lands on a known working control or halt. -/
theorem parent_step_valid (c d : Configuration) (h : fullStep parent c = some d) :
    validControl d.state := by
  cases hr : lookup parent c.state (c.tape c.pos) with
  | none => simp [fullStep, hr] at h
  | some row =>
    have hmem : row ∈ parent := List.mem_of_find?_eq_some hr
    have hrow := (List.all_eq_true.mp finite_controls.1) row hmem
    have hg : ((lookup parent row.state false).isSome = true ∧
        (lookup parent row.state true).isSome = true) ∧
        (row.target = 254 ∨ knownControl row.target = true) := by
      simpa [controlGood, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] using hrow
    have ht := hg.2
    have hd : d = ⟨row.target, c.pos + (if row.right then 1 else -1),
        Function.update c.tape c.pos row.write⟩ := by
      simpa [fullStep, hr] using h.symm
    subst d
    exact ht

theorem start_valid (t : Int → Bool) (p : Int) :
    validControl (Configuration.mk 74 p t).state := Or.inr finite_controls.2.1

/-- The parent has a next step at every valid nonhalting control, on every tape. -/
theorem parent_total (c : Configuration) (hv : validControl c.state) (hh : c.state ≠ 254) :
    ∃ d, fullStep parent c = some d := by
  have hk : knownControl c.state = true := hv.resolve_left hh
  obtain ⟨row, hmem, heq⟩ := (List.any_eq_true.mp hk)
  have hr : row.state = c.state := by simpa [beq_iff_eq] using heq
  have hrow := (List.all_eq_true.mp finite_controls.1) row hmem
  have hbits : (lookup parent c.state false).isSome = true ∧
      (lookup parent c.state true).isSome = true := by
    have h : ((lookup parent row.state false).isSome = true ∧
        (lookup parent row.state true).isSome = true) ∧
        (row.target = 254 ∨ knownControl row.target = true) := by
      simpa [controlGood, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] using hrow
    simpa [hr] using h.1
  cases hbit : c.tape c.pos with
  | false =>
    cases hx : lookup parent c.state false with
    | none => simp [hx] at hbits
    | some out => exact ⟨⟨out.target, c.pos + (if out.right then 1 else -1),
        Function.update c.tape c.pos out.write⟩, by simp [fullStep, hbit, hx]⟩
  | true =>
    cases hx : lookup parent c.state true with
    | none => simp [hx] at hbits
    | some out => exact ⟨⟨out.target, c.pos + (if out.right then 1 else -1),
        Function.update c.tape c.pos out.write⟩, by simp [fullStep, hbit, hx]⟩

theorem halt_maps : project 254 = 254 := finite_controls.2.2.2.2

theorem child_halt_stuck (c : Configuration) (hc : c.state = 254) : fullStep folded c = none := by
  cases hbit : c.tape c.pos <;> simp [fullStep, hc, hbit, finite_controls.2.2.1, finite_controls.2.2.2.1]

#print axioms parent_step_valid
#print axioms parent_total
#print axioms child_halt_stuck
end PA195LocalQuotient
