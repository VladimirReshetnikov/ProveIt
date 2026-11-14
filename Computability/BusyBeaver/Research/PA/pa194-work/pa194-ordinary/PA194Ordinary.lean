import PA194AllTape
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194LocalQuotient

/-- Outside the seven reader pairs, a parent step is exactly one folded step,
for arbitrary head position and arbitrary complete tape. -/
theorem ordinary_step_all_tapes (q : Nat) (p : Int) (t : Int → Bool)
    (hordinary : folds.any (fun pair => q == pair.1 || q == pair.2) = false)
    (a : Configuration) (h : fullStep parent ⟨q, p, t⟩ = some a) :
    fullStep folded ⟨project q, p, t⟩ = some ⟨project a.state, a.pos, a.tape⟩ := by
  cases hr : lookup parent q (t p) with
  | none => simp [fullStep, hr] at h
  | some r =>
    have hmem : r ∈ parent := List.mem_of_find?_eq_some hr
    have hmatch : r.state = q ∧ r.read = t p := by
      have hm := List.find?_some hr
      simpa [lookup, Bool.and_eq_true, beq_iff_eq] using hm
    have hg : parent.all ordinaryGood = true := by
      rcases finite_certificate with ⟨_, _, _, _, _, _, _, _, _, _, hg⟩
      exact hg
    have hg' := (List.all_eq_true.mp hg) r hmem
    have hor' : folds.any (fun pair => r.state == pair.1 || r.state == pair.2) = false := by
      simpa [hmatch.1] using hordinary
    cases hs : lookup folded (project r.state) r.read with
    | none => simp [ordinaryGood, hor', hs] at hg'
    | some s =>
      have hs' : (s.write = r.write ∧ s.right = r.right) ∧ s.target = project r.target := by
        simpa [ordinaryGood, hor', hs, Bool.and_eq_true, beq_iff_eq] using hg'
      have ha : a = ⟨r.target, p + (if r.right then 1 else -1), Function.update t p r.write⟩ := by
        simpa [fullStep, hr] using h.symm
      subst a
      simp only [fullStep, Option.bind_eq_bind]
      have hlookup : lookup folded (project q) (t p) = some s := by
        simpa [hmatch.1, hmatch.2] using hs
      simp [hlookup, hs'.1.1, hs'.1.2, hs'.2]

#print axioms ordinary_step_all_tapes
end PA194LocalQuotient
