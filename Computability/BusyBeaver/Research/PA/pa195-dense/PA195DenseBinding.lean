import PA195DenseData
import PA195Control
import PA195GenericTrace
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA195LocalQuotient

/-- The state-map image of an entire dense-machine configuration. -/
def mapDense (c : Configuration) : Configuration := ⟨label c.state, c.pos, c.tape⟩
def denseValid (c : Configuration) : Prop := c.state ≤ 195

/-- Every actual dense row agrees with its native row in write, direction and
state-map image of target. -/
theorem dense_row_binding (r : Row) (hmem : r ∈ dense) :
    ∃ s : Row, lookup folded (label r.state) r.read = some s ∧
      s.write = r.write ∧ s.right = r.right ∧ s.target = label r.target := by
  have hall : dense.all denseGood = true := by
    rcases finite_certificate with ⟨_, _, _, _, _, h, _, _, _, _, _⟩
    exact h
  have hr := (List.all_eq_true.mp hall) r hmem
  cases hq : labels[r.state]? with
  | none => simp [denseGood, hq] at hr
  | some q =>
    cases ht : labels[r.target]? with
    | none => simp [denseGood, hq, ht] at hr
    | some t =>
      cases hs : lookup folded q r.read with
      | none => simp [denseGood, hq, ht, hs] at hr
      | some s =>
        have hb : (s.write = r.write ∧ s.right = r.right) ∧ s.target = t := by
          simpa [denseGood, hq, ht, hs, Bool.and_eq_true, beq_iff_eq] using hr
        refine ⟨s, ?_, hb.1.1, hb.1.2, ?_⟩
        · simpa [label, hq] using hs
        · simpa [label, ht] using hb.2

/-- Every dense step maps to exactly one native step on the same full tape. -/
theorem dense_step_binding (c d : Configuration) (h : fullStep dense c = some d) :
    fullStep folded (mapDense c) = some (mapDense d) := by
  cases hr : lookup dense c.state (c.tape c.pos) with
  | none => simp [fullStep, hr] at h
  | some r =>
    have hmem : r ∈ dense := List.mem_of_find?_eq_some hr
    have hmatch : r.state = c.state ∧ r.read = c.tape c.pos := by
      have hm := List.find?_some hr
      simpa [lookup, Bool.and_eq_true, beq_iff_eq] using hm
    obtain ⟨s, hs, hw, hd, ht⟩ := dense_row_binding r hmem
    have hlookup : lookup folded (label c.state) (c.tape c.pos) = some s := by
      simpa [hmatch.1, hmatch.2] using hs
    have heq : d = ⟨r.target, c.pos + (if r.right then 1 else -1),
        Function.update c.tape c.pos r.write⟩ := by
      simpa [fullStep, hr] using h.symm
    subst d
    simp [fullStep, mapDense, hlookup, hw, hd, ht]

theorem dense_step_valid (c d : Configuration) (h : fullStep dense c = some d) : denseValid d := by
  cases hr : lookup dense c.state (c.tape c.pos) with
  | none => simp [fullStep, hr] at h
  | some r =>
    have hmem : r ∈ dense := List.mem_of_find?_eq_some hr
    have hgood := (List.all_eq_true.mp dense_control_certificate.1) r hmem
    have hp : r.state < 195 ∧ r.target ≤ 195 := by
      simpa [denseRowGood, Bool.and_eq_true] using hgood
    have ht := hp.2
    have heq : d = ⟨r.target, c.pos + (if r.right then 1 else -1),
        Function.update c.tape c.pos r.write⟩ := by
      simpa [fullStep, hr] using h.symm
    subst d
    exact ht

theorem dense_total (c : Configuration) (hv : denseValid c) (hh : c.state ≠ 195) :
    ∃ d, fullStep dense c = some d := by
  have hq : c.state < 195 := by unfold denseValid at hv; omega
  have hmem : c.state ∈ List.range 195 := List.mem_range.mpr hq
  have hgood := (List.all_eq_true.mp dense_control_certificate.2.1) c.state hmem
  have hbits : (lookup dense c.state false).isSome = true ∧
      (lookup dense c.state true).isSome = true := by
    simpa [denseControlGood, Bool.and_eq_true] using hgood
  cases hbit : c.tape c.pos with
  | false =>
    cases hr : lookup dense c.state false with
    | none => simp [hr] at hbits
    | some r => exact ⟨⟨r.target, c.pos + (if r.right then 1 else -1),
        Function.update c.tape c.pos r.write⟩, by simp [fullStep, hbit, hr]⟩
  | true =>
    cases hr : lookup dense c.state true with
    | none => simp [hr] at hbits
    | some r => exact ⟨⟨r.target, c.pos + (if r.right then 1 else -1),
        Function.update c.tape c.pos r.write⟩, by simp [fullStep, hbit, hr]⟩

/-- Exact halting equivalence of the dense 0/195 machine and its native
74/254 table for any initial tape and head position. -/
theorem dense_native_halts (p : Int) (t : Int → Bool) :
    PA195GenericTrace.Halts (fullStep dense) (fun c => c.state = 195) ⟨0,p,t⟩ ↔
    PA195GenericTrace.Halts (fullStep folded) (fun c => c.state = 254) ⟨74,p,t⟩ := by
  have h := PA195GenericTrace.halts_iff (fullStep dense) (fullStep folded) mapDense denseValid
    (fun c => c.state = 195) (fun c => c.state = 254)
    (fun c d _ => dense_step_valid c d)
    (fun c d _ hs => ⟨1, by decide, by simpa [PA195GenericTrace.run] using dense_step_binding c d hs⟩)
    dense_total
    (fun c hc => by simp [mapDense, hc, dense_control_certificate.2.2.2])
    child_halt_stuck ⟨0,p,t⟩ (by change 0 ≤ 195; decide)
  simpa [mapDense, dense_control_certificate.2.2.1] using h

#print axioms dense_step_binding
#print axioms dense_step_valid
#print axioms dense_total
#print axioms dense_native_halts
end PA195LocalQuotient
