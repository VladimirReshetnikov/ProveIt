import PA194ADOrdinary
set_option autoImplicit false
namespace PA194ADTable

abbrev Conf := Nat × Nat × Nat

def rowIndex (c : Conf) : Nat := 2 * c.1 + c.2.2 % 2

def next (rows : List Action) (c : Conf) : Conf :=
  if c.1 < 194 then
    let a := rows.getD (rowIndex c) (0,0,194)
    if a.2.1 = 1 then (a.2.2,2*c.2.1+a.1,c.2.2/2)
    else (a.2.2,c.2.1/2,c.2.1%2+2*(a.1+2*(c.2.2/2)))
  else c

def ordinary (c : Conf) : Prop := rowIndex c ≠ 219 ∧ rowIndex c ≠ 221 ∧ rowIndex c ≠ 249

theorem next_eq (c : Conf) (h : ordinary c) :
    next adRows c = next PA194Rows.rows c := by
  have hr := ordinary_rows (rowIndex c) h.1 h.2.1 h.2.2
  simp only [next, hr]

def run (rows : List Action) (c : Conf) : Nat → Conf
  | 0 => c
  | n+1 => next rows (run rows c n)

/-- Any initial configuration has exactly the same execution until a modified row is read. -/
theorem run_eq_until (c : Conf) (n : Nat)
    (h : ∀ k < n, ordinary (run PA194Rows.rows c k)) :
    run adRows c n = run PA194Rows.rows c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp : ∀ k < n, ordinary (run PA194Rows.rows c k) := by
      intro k hk
      exact h k (Nat.lt_trans hk (Nat.lt_succ_self n))
    have hs := h n (Nat.lt_succ_self n)
    simp only [run]
    rw [ih hp, next_eq _ hs]

#print axioms next_eq
#print axioms run_eq_until
end PA194ADTable
