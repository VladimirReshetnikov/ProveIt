import PA194Translate
import PA194Ordinary
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194LocalQuotient

def History (c : Configuration) : Prop :=
  ∀ pair ∈ folds,
    (c.state = pair.1 → c.tape (c.pos - 1) = false) ∧
    (c.state = pair.2 → c.tape (c.pos - 1) = true)

theorem history_start (t : Int → Bool) (p : Int) : History ⟨74, p, t⟩ := by
  simp [History, folds]

theorem history_step (c a : Configuration) (h : fullStep parent c = some a) : History a := by
  cases hr : lookup parent c.state (c.tape c.pos) with
  | none => simp [fullStep, hr] at h
  | some r =>
    have hmem : r ∈ parent := List.mem_of_find?_eq_some hr
    have hall : parent.all incomingGood = true := by
      rcases finite_certificate with ⟨_, _, _, _, _, _, _, _, _, hall, _⟩
      exact hall
    have hgood := (List.all_eq_true.mp hall) r hmem
    have ha : a = ⟨r.target, c.pos + (if r.right then 1 else -1),
        Function.update c.tape c.pos r.write⟩ := by
      simpa [fullStep, hr] using h.symm
    subst a
    intro pair hpair
    have hp := (List.all_eq_true.mp hgood) pair hpair
    constructor
    · intro ht
      have hw : r.write = false ∧ r.right = true := by
        have hs : (¬r.target = pair.1 ∨ r.write = false ∧ r.right = true) ∧
            (¬r.target = pair.2 ∨ r.write = true ∧ r.right = true) := by
          simpa [incomingGood, Bool.and_eq_true] using hp
        exact hs.1.resolve_left (fun hne => hne ht)
      rcases hw with ⟨hw, hd⟩
      have hpos : c.pos + (if r.right then 1 else -1) - 1 = c.pos := by
        simp [hd]
      simp [hpos, hw]
    · intro ht
      have hw : r.write = true ∧ r.right = true := by
        have hs : (¬r.target = pair.1 ∨ r.write = false ∧ r.right = true) ∧
            (¬r.target = pair.2 ∨ r.write = true ∧ r.right = true) := by
          simpa [incomingGood, Bool.and_eq_true] using hp
        exact hs.2.resolve_left (fun hne => hne ht)
      rcases hw with ⟨hw, hd⟩
      have hpos : c.pos + (if r.right then 1 else -1) - 1 = c.pos := by
        simp [hd]
      simp [hpos, hw]

theorem cases_cover_left (pair : Nat × Nat) (hp : pair ∈ folds) (bit : Bool) :
    ∃ c ∈ cases, c.state = pair.1 ∧ c.left = false ∧ c.read = bit := by
  have hcov : casesCover = true := by
    rcases finite_certificate with ⟨_, _, _, _, _, _, _, h, _, _, _⟩
    exact h
  have hall : folds.all (fun pair => [false, true].all (fun bit =>
    cases.any (fun c => c.state == pair.1 && !c.left && c.read == bit) &&
    cases.any (fun c => c.state == pair.2 && c.left && c.read == bit))) = true := hcov
  have hp' := (List.all_eq_true.mp hall) pair hp
  have hb : bit ∈ [false, true] := by cases bit <;> simp
  have hr := (List.all_eq_true.mp hp') bit hb
  simp only [Bool.and_eq_true] at hr
  have hl : cases.any (fun c => c.state == pair.1 && !c.left && c.read == bit) = true := by
    simpa [Bool.and_eq_true] using hr.1
  obtain ⟨c, hc, htest⟩ := List.any_eq_true.mp hl
  refine ⟨c, hc, ?_⟩
  simpa [Bool.and_eq_true, beq_iff_eq, and_assoc] using htest

theorem cases_cover_right (pair : Nat × Nat) (hp : pair ∈ folds) (bit : Bool) :
    ∃ c ∈ cases, c.state = pair.2 ∧ c.left = true ∧ c.read = bit := by
  have hcov : casesCover = true := by
    rcases finite_certificate with ⟨_, _, _, _, _, _, _, h, _, _, _⟩
    exact h
  have hall : folds.all (fun pair => [false, true].all (fun bit =>
    cases.any (fun c => c.state == pair.1 && !c.left && c.read == bit) &&
    cases.any (fun c => c.state == pair.2 && c.left && c.read == bit))) = true := hcov
  have hp' := (List.all_eq_true.mp hall) pair hp
  have hb : bit ∈ [false, true] := by cases bit <;> simp
  have hr := (List.all_eq_true.mp hp') bit hb
  simp only [Bool.and_eq_true] at hr
  have hl : cases.any (fun c => c.state == pair.2 && c.left && c.read == bit) = true := by
    simpa [Bool.and_eq_true] using hr.2
  obtain ⟨c, hc, htest⟩ := List.any_eq_true.mp hl
  refine ⟨c, hc, ?_⟩
  simpa [Bool.and_eq_true, beq_iff_eq, and_assoc] using htest

theorem cases_duration_positive : ∀ c ∈ cases, 0 < c.duration := by decide +kernel

/-- A parent step with correct reader history is simulated by a nonempty
folded run on the exact same tape, from any head position. -/
theorem simulation_step (c a : Configuration) (hh : History c)
    (hstep : fullStep parent c = some a) :
    ∃ n > 0, fullRun folded n ⟨project c.state, c.pos, c.tape⟩ =
      some ⟨project a.state, a.pos, a.tape⟩ := by
  cases c with
  | mk q p t =>
    by_cases ho : folds.any (fun pair => q == pair.1 || q == pair.2) = false
    · refine ⟨1, by decide, ?_⟩
      simpa [fullRun] using ordinary_step_all_tapes q p t ho a hstep
    · have ht : folds.any (fun pair => q == pair.1 || q == pair.2) = true := by
        cases h : folds.any (fun pair => q == pair.1 || q == pair.2) <;> simp_all
      obtain ⟨pair, hp, hmatch⟩ := List.any_eq_true.mp ht
      have hm : q = pair.1 ∨ q = pair.2 := by
        simpa [Bool.or_eq_true, beq_iff_eq] using hmatch
      rcases hm with hq | hq
      · obtain ⟨v, hv, hstate, hleft, hread⟩ := cases_cover_left pair hp (t p)
        have hhist : t (p - 1) = v.left := by
          rw [hleft]
          exact (hh pair hp).1 hq
        have hcur : t p = v.read := hread.symm
        obtain ⟨a', ha', hb'⟩ := checked_case_any_head v hv p t hhist hcur
        have haeq : a' = a := by
          rw [hstate, ← hq] at ha'
          exact Option.some.inj (ha'.symm.trans hstep)
        subst a'
        refine ⟨v.duration, cases_duration_positive v hv, ?_⟩
        simpa [hstate, ← hq] using hb'
      · obtain ⟨v, hv, hstate, hleft, hread⟩ := cases_cover_right pair hp (t p)
        have hhist : t (p - 1) = v.left := by
          rw [hleft]
          exact (hh pair hp).2 hq
        have hcur : t p = v.read := hread.symm
        obtain ⟨a', ha', hb'⟩ := checked_case_any_head v hv p t hhist hcur
        have haeq : a' = a := by
          rw [hstate, ← hq] at ha'
          exact Option.some.inj (ha'.symm.trans hstep)
        subst a'
        refine ⟨v.duration, cases_duration_positive v hv, ?_⟩
        simpa [hstate, ← hq] using hb'

#print axioms simulation_step
#print axioms cases_duration_positive
#print axioms cases_cover_left
#print axioms cases_cover_right
#print axioms history_start
#print axioms history_step
end PA194LocalQuotient
