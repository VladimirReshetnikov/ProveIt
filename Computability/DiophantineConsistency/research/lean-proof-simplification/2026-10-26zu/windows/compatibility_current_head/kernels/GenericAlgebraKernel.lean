import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Order.Ring.Nat

/-!
An ordered-window eliminator shared by quotient and max-square-pairing
uniqueness. The carrier of indices need not be well founded or externally
finite; the codomain needs only a preorder.
-/
namespace ProofDelta.OrderedWindow

variable {I C : Type*} [LinearOrder I] [Preorder C]

/-- Two adjacent half-open monotone windows containing the same value have
identical indices. No strict monotonicity assumption on `base` is needed. -/
theorem index_unique (succ : I → I)
    (step_le : ∀ {a b : I}, a < b → succ a ≤ b)
    (base : I → C) (mono : Monotone base)
    {a b : I} {x : C}
    (ha : base a ≤ x) (ha' : x < base (succ a))
    (hb : base b ≤ x) (hb' : x < base (succ b)) : a = b := by
  apply le_antisymm
  · exact le_of_not_gt (fun h => (not_lt_of_ge ha) (hb'.trans_le (mono (step_le h))))
  · exact le_of_not_gt (fun h => (not_lt_of_ge hb) (ha'.trans_le (mono (step_le h))))

section Semiring
variable {R : Type*} [CommSemiring R] [LinearOrder R]
  [CanonicallyOrderedAdd R] [IsStrictOrderedRing R]

/-- Post-adoption client: the existing successor bridge is a hypothesis. -/
theorem division_unique
    (step_le : ∀ {a b : R}, a < b → a + 1 ≤ b)
    {q r q' r' n d : R}
    (h : n = q * d + r ∧ r < d)
    (h' : n = q' * d + r' ∧ r' < d) : q = q' ∧ r = r' := by
  have window {a b : R} (he : n = a * d + b) (hb : b < d) :
      a * d ≤ n ∧ n < (a + 1) * d := by
    rw [he]
    exact ⟨le_self_add, by simpa only [add_mul, one_mul, add_comm] using add_lt_add_left hb (a * d)⟩
  have hq := index_unique (fun a : R => a + 1) step_le (fun a => a * d)
    (fun _ _ h => mul_le_mul_of_nonneg_right h (zero_le : (0 : R) ≤ d))
    (window h.1 h.2).1 (window h.1 h.2).2 (window h'.1 h'.2).1 (window h'.1 h'.2).2
  subst q'
  exact ⟨rfl, add_left_cancel (h.1.symm.trans h'.1)⟩

/-- The max-square pairing client needs only its already proved bounds. -/
theorem square_index_unique
    (step_le : ∀ {a b : R}, a < b → a + 1 ≤ b)
    {a b x : R} (ha : a * a ≤ x) (ha' : x < (a + 1) * (a + 1))
    (hb : b * b ≤ x) (hb' : x < (b + 1) * (b + 1)) : a = b :=
  index_unique (fun a : R => a + 1) step_le (fun a => a * a)
    (fun _ _ h => mul_le_mul h h (zero_le : (0 : R) ≤ _) (zero_le : (0 : R) ≤ _))
    ha ha' hb hb'

/-- Immediate endpoint edit, with no shared-helper integration required. -/
theorem quotient_not_lt_direct
    (step_le : ∀ {a b : R}, a < b → a + 1 ≤ b)
    {q r q' r' n d : R}
    (h : n = q * d + r ∧ r < d)
    (h' : n = q' * d + r' ∧ r' < d) : ¬ q < q' := by
  intro hq
  have upper : n < (q + 1) * d := by
    rw [h.1, add_mul, one_mul]
    simpa only [add_comm] using add_lt_add_left h.2 (q * d)
  exact (not_lt_of_ge (le_self_add.trans h'.1.ge))
    (upper.trans_le (mul_le_mul_of_nonneg_right (step_le hq) (zero_le : (0 : R) ≤ d)))

end Semiring

example {q r q' r' n d : Nat}
    (h : n = q * d + r ∧ r < d)
    (h' : n = q' * d + r' ∧ r' < d) : q = q' ∧ r = r' :=
  division_unique (fun h => Nat.succ_le_of_lt h) h h'

#print axioms index_unique
#print axioms division_unique
#print axioms square_index_unique
#print axioms quotient_not_lt_direct
end ProofDelta.OrderedWindow
