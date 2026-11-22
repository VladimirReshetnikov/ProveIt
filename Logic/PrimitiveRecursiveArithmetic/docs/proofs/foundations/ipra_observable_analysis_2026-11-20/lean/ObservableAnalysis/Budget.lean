import Std

/-!
# A finite transposed error-budget certificate

All sums below are explicit primitive recursions over a natural bound.  The
theorems are Lean metatheorems.  Fixed primitive-recursive rational data and
quantifier-free loop invariants are still required for an iPRA instance.
-/

namespace ObservableAnalysis

/-- A rational sum with the exclusive upper bound `n`. -/
def sumQ (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => sumQ f n + f n

theorem sumQ_congr (n : Nat) (f g : Nat → Rat)
    (h : ∀ i, i < n → f i = g i) : sumQ f n = sumQ g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumQ]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem sumQ_add (f g : Nat → Rat) (n : Nat) :
    sumQ (fun i => f i + g i) n = sumQ f n + sumQ g n := by
  induction n with
  | zero => simp only [sumQ, Rat.add_zero]
  | succ n ih =>
    simp only [sumQ, ih]
    rw [Rat.add_assoc, ← Rat.add_assoc (sumQ g n), Rat.add_comm (sumQ g n) (f n),
      Rat.add_assoc, ← Rat.add_assoc]

theorem sumQ_mul (f : Nat → Rat) (a : Rat) (n : Nat) :
    sumQ (fun i => f i * a) n = sumQ f n * a := by
  induction n with
  | zero => simp only [sumQ, Rat.zero_mul]
  | succ n ih => simp only [sumQ, ih, Rat.add_mul]

theorem mul_sumQ (a : Rat) (f : Nat → Rat) (n : Nat) :
    sumQ (fun i => a * f i) n = a * sumQ f n := by
  induction n with
  | zero => simp only [sumQ, Rat.mul_zero]
  | succ n ih => simp only [sumQ, ih, Rat.mul_add]

theorem sumQ_zero (n : Nat) : sumQ (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumQ, ih, Rat.add_zero]

/-- Exact finite Fubini identity, without any infinite sum or measure object. -/
theorem sumQ_exchange (f : Nat → Nat → Rat) (m n : Nat) :
    sumQ (fun i => sumQ (f i) n) m =
      sumQ (fun j => sumQ (fun i => f i j) m) n := by
  induction m with
  | zero => simp only [sumQ, sumQ_zero]
  | succ m ih =>
    simp only [sumQ]
    rw [ih, sumQ_add]

private theorem add_le_add {a b c d : Rat} (hab : a ≤ b) (hcd : c ≤ d) :
    a + c ≤ b + d := by
  exact Rat.le_trans (Rat.add_le_add_right.mpr hab) (Rat.add_le_add_left.mpr hcd)

theorem sumQ_mono (f g : Nat → Rat) (n : Nat)
    (h : ∀ i, i < n → f i ≤ g i) : sumQ f n ≤ sumQ g n := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
    exact add_le_add (ih (fun i hi => h i (by omega))) (h n (by omega))

/--
The transposed budget certificate.  `L v u` is the amplification from input
`u` to output `v`; `delta v` is the new local error, and `b` selects the
desired final observations.  A nonnegative weight vector satisfying the
displayed finite balance converts local errors into the final bound.

Triangularity is not needed by this verification theorem.  It is what lets
the paper *produce* `W` by a bounded reverse traversal of an acyclic graph.
-/
theorem weighted_budget
    (n : Nat) (e delta b W : Nat → Rat) (L : Nat → Nat → Rat)
    (hW : ∀ v, v < n → 0 ≤ W v)
    (hlocal : ∀ v, v < n →
      e v ≤ delta v + sumQ (fun u => L v u * e u) n)
    (hbalance : ∀ u, u < n →
      W u = b u + sumQ (fun v => W v * L v u) n) :
    sumQ (fun u => b u * e u) n ≤ sumQ (fun v => W v * delta v) n := by
  let cross := sumQ (fun v => sumQ (fun u => W v * L v u * e u) n) n
  have weightedLocal : sumQ (fun v => W v * e v) n ≤
      sumQ (fun v => W v * delta v) n + cross := by
    have h := sumQ_mono (fun v => W v * e v)
      (fun v => W v * (delta v + sumQ (fun u => L v u * e u) n)) n
      (fun v hv => Rat.mul_le_mul_of_nonneg_left (hlocal v hv) (hW v hv))
    have heq : sumQ
        (fun v => W v * (delta v + sumQ (fun u => L v u * e u) n)) n =
        sumQ (fun v => W v * delta v) n + cross := by
      unfold cross
      rw [← sumQ_add]
      apply sumQ_congr
      intro v _
      rw [Rat.mul_add, ← mul_sumQ]
      congr 1
      apply sumQ_congr
      intro u _
      exact (Rat.mul_assoc _ _ _).symm
    rw [heq] at h
    exact h
  have weightedBalance : sumQ (fun u => W u * e u) n =
      sumQ (fun u => b u * e u) n + cross := by
    have heq : sumQ (fun u => W u * e u) n =
        sumQ (fun u => b u * e u) n +
          sumQ (fun u => sumQ (fun v => W v * L v u * e u) n) n := by
      rw [← sumQ_add]
      apply sumQ_congr
      intro u hu
      rw [hbalance u hu, Rat.add_mul, sumQ_mul]
    rw [heq]
    congr 1
    exact sumQ_exchange (fun u v => W v * L v u * e u) n n
  rw [weightedBalance] at weightedLocal
  exact Rat.add_le_add_right.mp weightedLocal

/--
A verified nonnegative *supersolution* is sufficient.  This variant may
certify a cyclic error system, even when reverse traversal cannot produce
an exact solution.  Nonnegativity of `e` is needed for the comparison.
-/
theorem weighted_budget_supersolution
    (n : Nat) (e delta b W : Nat → Rat) (L : Nat → Nat → Rat)
    (he : ∀ u, u < n → 0 ≤ e u)
    (hW : ∀ v, v < n → 0 ≤ W v)
    (hlocal : ∀ v, v < n →
      e v ≤ delta v + sumQ (fun u => L v u * e u) n)
    (hbalance : ∀ u, u < n →
      b u + sumQ (fun v => W v * L v u) n ≤ W u) :
    sumQ (fun u => b u * e u) n ≤ sumQ (fun v => W v * delta v) n := by
  let b' := fun u => W u - sumQ (fun v => W v * L v u) n
  have hexact := weighted_budget n e delta b' W L hW hlocal
    (fun _ _ => Rat.sub_add_cancel.symm)
  have hcompare := sumQ_mono (fun u => b u * e u) (fun u => b' u * e u) n
    (fun u hu => Rat.mul_le_mul_of_nonneg_right
      (Rat.add_le_iff_le_sub.mp (hbalance u hu)) (he u hu))
  exact Rat.le_trans hcompare hexact

#print axioms sumQ_exchange
#print axioms weighted_budget
#print axioms weighted_budget_supersolution

end ObservableAnalysis
