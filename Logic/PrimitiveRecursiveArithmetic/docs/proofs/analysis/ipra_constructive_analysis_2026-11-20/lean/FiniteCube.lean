import BitIntegral

namespace BudgetAnalysis.BitIntegral

def put (o : Oracle) (q : Nat) (b : Bool) : Oracle :=
  fun i => if i = q then b else o i

def cube : List Nat → Oracle → List Oracle
  | [], o => [o]
  | q :: qs, o => cube qs (put o q false) ++ cube qs (put o q true)

theorem cube_length (qs : List Nat) (o : Oracle) :
    (cube qs o).length = 2 ^ qs.length := by
  induction qs generalizing o with
  | nil => rfl
  | cons q qs ih => simp [cube, ih, Nat.pow_succ, Nat.mul_two]

theorem cube_fixed (qs : List Nat) (o : Oracle) (q : Nat) (fixed : q ∉ qs) :
    ∀ x ∈ cube qs o, x q = o q := by
  induction qs generalizing o with
  | nil => simp [cube]
  | cons i qs ih =>
    intro x hx
    have ne : q ≠ i := fun e => fixed (by simp [e])
    have no : q ∉ qs := fun mem => fixed (by simp [mem])
    cases List.mem_append.mp hx with
    | inl h => simpa [put, ne] using ih (put o i false) no x h
    | inr h => simpa [put, ne] using ih (put o i true) no x h

theorem side_constant (xs : List Oracle) (q : Nat) (a b : Bool)
    (h : ∀ x ∈ xs, x q = a) :
    side xs q b = if a = b then xs else [] := by
  induction xs with
  | nil => simp [side]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    cases a <;> cases b <;> simp [side, hx] at ht ⊢ <;> assumption

theorem put_comm {q i : Nat} (hne : q ≠ i) (o : Oracle) (a b : Bool) :
    put (put o i a) q b = put (put o q b) i a := by
  funext j
  by_cases ji : j = i
  · subst j
    simp [put, Ne.symm hne]
  · simp [put, ji]

theorem cube_slice (qs : List Nat) (nd : qs.Nodup) (o : Oracle) (q : Nat)
    (mem : q ∈ qs) (b : Bool) :
    side (cube qs o) q b = cube (qs.erase q) (put o q b) := by
  induction qs generalizing o with
  | nil => simp at mem
  | cons i qs ih =>
    obtain ⟨ni, tail⟩ := List.nodup_cons.mp nd
    by_cases eq : i = q
    · subst i
      have C (a : Bool) : ∀ x ∈ cube qs (put o q a), x q = a := by
        intro x hx
        simpa [put] using cube_fixed qs (put o q a) q ni x hx
      simp only [cube, side, List.filter_append, List.erase_cons_head]
      change side (cube qs (put o q false)) q b ++ side (cube qs (put o q true)) q b = _
      rw [side_constant _ q false b (C false), side_constant _ q true b (C true)]
      cases b <;> simp
    · have hmem : q ∈ qs := (List.mem_cons.mp mem).resolve_left (Ne.symm eq)
      have beq : ¬(i == q) := by simpa using eq
      simp only [cube, side, List.filter_append, List.erase_cons_tail beq]
      change side (cube qs (put o i false)) q b ++ side (cube qs (put o i true)) q b = _
      rw [ih tail _ hmem, ih tail _ hmem, put_comm (Ne.symm eq), put_comm (Ne.symm eq)]

/-- Exactly the coordinates in qs are free, all others use o. -/
def context (qs : List Nat) (o : Oracle) : Hist :=
  fun q => if q ∈ qs then none else some (o q)

theorem record_context (qs : List Nat) (nd : qs.Nodup) (o : Oracle)
    (q : Nat) (b : Bool) :
    record (context qs o) q b = context (qs.erase q) (put o q b) := by
  funext i
  by_cases e : i = q
  · subst i
    simp [record, context, put, List.Nodup.not_mem_erase nd]
  · have iffMem : i ∈ qs.erase q ↔ i ∈ qs := List.mem_erase_of_ne e
    simp [record, context, put, e, iffMem]

theorem cube_calibrated (t : T) (qs : List Nat) (nd : qs.Nodup) (o : Oracle) :
    Calibrated t (context qs o) (cube qs o) := by
  induction t generalizing qs o with
  | ret => trivial
  | ask q next ih =>
    by_cases mem : q ∈ qs
    · have fresh : context qs o q = none := by simp [context, mem]
      simp only [Calibrated, fresh]
      have lengths (b : Bool) :
          (side (cube qs o) q b).length = (cube qs o).length / 2 := by
        rw [cube_slice qs nd o q mem b, cube_length, cube_length]
        have len : qs.length = (qs.erase q).length + 1 := by
          have pos := List.length_pos_of_mem mem
          have dif := List.length_erase_of_mem mem
          omega
        rw [len, Nat.pow_succ]
        omega
      refine ⟨lengths false, lengths true, ?_, ?_⟩ <;>
        rw [cube_slice qs nd o q mem, record_context qs nd] <;>
        exact ih _ _ (nd.erase _) _
    · have known : context qs o q = some (o q) := by simp [context, mem]
      simp only [Calibrated, known]
      exact ⟨cube_fixed qs o q mem, ih _ _ nd _⟩

theorem integrate_cube (t : T) (qs : List Nat) (nd : qs.Nodup) (o : Oracle) :
    weighted t (context qs o) (2 ^ qs.length) =
      total (fun x => Dialogue.eval x t) (cube qs o) := by
  simpa only [cube_length] using
    weighted_correct t (context qs o) (cube qs o) (cube_calibrated t qs nd o)

end BudgetAnalysis.BitIntegral
