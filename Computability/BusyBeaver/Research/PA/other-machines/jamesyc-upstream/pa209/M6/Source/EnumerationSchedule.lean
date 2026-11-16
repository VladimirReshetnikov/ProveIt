module
public import M6.Source.EnumerationCredit
@[expose] public section
namespace M6.Source.Enumeration

def schedule (n : Nat) : List Command := (List.range n).flatMap word

theorem weight_append (a b : List Command) : weight (a++b) = weight a + weight b := by
  induction a with
  | nil => simp [weight]
  | cons c a ih => simp [weight,ih,Int.add_assoc]

theorem schedule_succ (n : Nat) : schedule (n+1) = schedule n ++ word n := by
  simp [schedule,List.range_succ]

theorem schedule_weight (n : Nat) : weight (schedule n) = balance n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [schedule_succ,weight_append,ih]
    rfl

private theorem prefix_append_cases {a b q : List Command} (h : q <+: a++b) :
    q <+: a ∨ ∃ p, q = a++p ∧ p <+: b := by
  rcases List.prefix_or_prefix_of_prefix h (List.prefix_append a b) with hq | ha
  · exact Or.inl hq
  · rcases ha with ⟨p,hp⟩
    refine Or.inr ⟨p,hp.symm,?_⟩
    rw [← hp] at h
    exact (List.prefix_append_right_inj a).mp h

/-- Every ordinary list prefix of the finite enumeration schedule is safe;
no coverage premise or arithmetic-prefix representation is assumed. -/
theorem schedule_prefix_credit (n : Nat) (q : List Command) (hq : q <+: schedule n) :
    -3 ≤ weight q := by
  induction n with
  | zero =>
    have he : q = [] := List.prefix_nil.mp hq
    simp [he,weight]
  | succ n ih =>
    rw [schedule_succ] at hq
    rcases prefix_append_cases hq with hq | ⟨p,rfl,hp⟩
    · exact ih hq
    · rcases hp with ⟨rest,hr⟩
      rw [weight_append,schedule_weight]
      exact every_prefix_credit n p rest hr.symm

/-- Includes an arbitrary completed prefix of the current word, and every
prefix ending earlier in that accumulated finite command stream. -/
theorem running_schedule_credit (n : Nat) (p rest q : List Command)
    (hp : word n = p++rest) (hq : q <+: schedule n ++ p) :
    -3 ≤ weight q := by
  apply schedule_prefix_credit (n+1) q
  rw [schedule_succ,hp,← List.append_assoc]
  exact hq.trans (List.prefix_append _ rest)

theorem running_schedule_initial_credit (n : Nat) (p rest q : List Command)
    (hp : word n = p++rest) (hq : q <+: schedule n ++ p) :
    6 ≤ 9 + weight q := by
  have h := running_schedule_credit n p rest q hp hq
  omega

#print axioms schedule_prefix_credit
#print axioms running_schedule_credit
end M6.Source.Enumeration

