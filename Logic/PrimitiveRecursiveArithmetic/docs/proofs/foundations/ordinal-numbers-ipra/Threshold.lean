import Limits

/-! The least index of a fundamental sequence strictly above a smaller term.
The search has fixed fuel equal to the node count of the smaller term. -/
namespace OrdinalPacket

/-- Advance the current index until the test succeeds or the fuel is used. -/
def firstWithin (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 =>
    let i := firstWithin p n
    if p i then i else i+1

private theorem firstWithin_inv (p : Nat → Bool) (n : Nat) :
    firstWithin p n ≤ n ∧
    (∀ j, j < firstWithin p n → p j = false) ∧
    (firstWithin p n = n ∨ p (firstWithin p n) = true) := by
  induction n with
  | zero => simp [firstWithin]
  | succ n ih =>
    rcases ih with ⟨bound, earlier, stopped⟩
    simp only [firstWithin]
    split
    next h =>
      exact ⟨Nat.le_succ_of_le bound, earlier, Or.inr h⟩
    next h =>
      have hf : p (firstWithin p n) = false := by simpa using h
      have he : firstWithin p n = n := stopped.resolve_right h
      refine ⟨Nat.succ_le_succ bound, ?_, Or.inl (congrArg Nat.succ he)⟩
      intro j hj
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj) with hje | hjl
      · exact hje ▸ hf
      · exact earlier _ hjl

def firstIndex (x y : T) : Nat :=
  firstWithin (fun n => decide (cmp y (fundamental x n) = .lt)) (nodes y)

private theorem above_mono (x y : T) (hl : endsPositive x = true)
    {i j : Nat} (hij : i ≤ j) (hi : cmp y (fundamental x i) = .lt) :
    cmp y (fundamental x j) = .lt := by
  induction hij with
  | refl => exact hi
  | step h ih =>
    exact cmp_trans _ _ _ ih (fundamental_increases _ _ _ (localStep_value _ _ hl)).1

theorem firstIndex_spec (x y : T) (n : Nat) (hl : endsPositive x = true)
    (hy : ok y = true) (h : cmp y x = .lt) :
    cmp y (fundamental x n) = .lt ↔ firstIndex x y ≤ n := by
  let p := fun k => decide (cmp y (fundamental x k) = .lt)
  let k := firstWithin p (nodes y)
  have inv := firstWithin_inv p (nodes y)
  have last : p (nodes y) = true := by
    exact decide_eq_true (cofinal_modulus _ _ _ hl hy h (Nat.le_refl _))
  have hit : p k = true := inv.2.2.elim (fun he => by change p (firstWithin p (nodes y)) = true; rw [he]; exact last) id
  change cmp y (fundamental x n) = .lt ↔ k ≤ n
  constructor
  · intro hn
    rcases Nat.lt_or_ge n k with hnk | hkn
    · have fail := inv.2.1 n hnk
      simp [p, hn] at fail
    · exact hkn
  · intro hkn
    exact above_mono _ _ hl hkn (of_decide_eq_true hit)

theorem firstIndex_bound (x y : T) : firstIndex x y ≤ nodes y :=
  (firstWithin_inv _ _).1

end OrdinalPacket
