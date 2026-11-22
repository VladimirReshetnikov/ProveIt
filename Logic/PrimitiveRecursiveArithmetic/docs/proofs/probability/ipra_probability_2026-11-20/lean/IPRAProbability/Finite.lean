import Std

/-!
A denominator-cleared finite probability kernel.
All mathematical declarations are proved.  No completion or iPRA
soundness theorem is asserted in this file.  Function parameters are
metatheoretic; an iPRA instance must supply primitive-recursive codes.
-/

namespace IPRAProbability

/-- A finite sum with an explicit natural bound. -/
def nsum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => nsum n f + f n

@[simp] theorem nsum_zero (f : Nat → Nat) : nsum 0 f = 0 := rfl
@[simp] theorem nsum_succ (n : Nat) (f : Nat → Nat) :
    nsum (n + 1) f = nsum n f + f n := rfl

theorem nsum_congr (n : Nat) {f g : Nat → Nat}
    (h : ∀ i, i < n → f i = g i) : nsum n f = nsum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [nsum_succ, nsum_succ,
      ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n))),
      h n (Nat.lt_succ_self n)]

theorem nsum_mono (n : Nat) {f g : Nat → Nat}
    (h : ∀ i, i < n → f i ≤ g i) : nsum n f ≤ nsum n g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    exact Nat.add_le_add
      (ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n))))
      (h n (Nat.lt_succ_self n))

@[simp] theorem nsum_const_zero (n : Nat) : nsum n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [nsum, ih]

theorem nsum_add (n : Nat) (f g : Nat → Nat) :
    nsum n (fun i => f i + g i) = nsum n f + nsum n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp [nsum, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem nsum_mul_left (n c : Nat) (f : Nat → Nat) :
    nsum n (fun i => c * f i) = c * nsum n f := by
  induction n with
  | zero => simp [nsum]
  | succ n ih => simp [nsum, ih, Nat.mul_add]

theorem nsum_mul_right (n c : Nat) (f : Nat → Nat) :
    nsum n (fun i => f i * c) = nsum n f * c := by
  simpa only [Nat.mul_comm] using nsum_mul_left n c f

theorem nsum_product (n m : Nat) (f g : Nat → Nat) :
    nsum n (fun i => nsum m (fun j => f i * g j)) =
      nsum n f * nsum m g := by
  calc
    _ = nsum n (fun i => f i * nsum m g) :=
      nsum_congr n (fun i _ => nsum_mul_left m (f i) g)
    _ = _ := nsum_mul_right n (nsum m g) f

/-- Unnormalized integer weight restricted to a decidable event. -/
def eventWeight (w : Nat → Nat) (A : Nat → Bool) (i : Nat) : Nat :=
  if A i then w i else 0

/-- Its probability is `mass n w A / nsum n w` when the denominator is positive. -/
def mass (n : Nat) (w : Nat → Nat) (A : Nat → Bool) : Nat :=
  nsum n (eventWeight w A)

@[simp] theorem mass_empty (n : Nat) (w : Nat → Nat) :
    mass n w (fun _ => false) = 0 := by
  change nsum n (fun _ => 0) = 0
  exact nsum_const_zero n

@[simp] theorem mass_univ (n : Nat) (w : Nat → Nat) :
    mass n w (fun _ => true) = nsum n w := rfl

theorem mass_mono (n : Nat) (w : Nat → Nat) (A B : Nat → Bool)
    (h : ∀ i, i < n → A i = true → B i = true) :
    mass n w A ≤ mass n w B := by
  apply nsum_mono
  intro i hi
  cases ha : A i with
  | false => simp [eventWeight, ha]
  | true => simp [eventWeight, ha, h i hi ha]

theorem mass_le_total (n : Nat) (w : Nat → Nat) (A : Nat → Bool) :
    mass n w A ≤ nsum n w := by
  simpa using mass_mono n w A (fun _ => true) (by intros; rfl)

theorem mass_complement (n : Nat) (w : Nat → Nat) (A : Nat → Bool) :
    mass n w A + mass n w (fun i => !(A i)) = nsum n w := by
  rw [mass, mass, ← nsum_add]
  apply nsum_congr
  intro i _
  cases ha : A i <;> simp [eventWeight, ha]

theorem union_bound (n : Nat) (w : Nat → Nat) (A B : Nat → Bool) :
    mass n w (fun i => A i || B i) ≤ mass n w A + mass n w B := by
  rw [mass, mass, mass, ← nsum_add]
  apply nsum_mono
  intro i _
  cases ha : A i <;> cases hb : B i <;> simp [eventWeight, ha, hb]

theorem disjoint_additivity (n : Nat) (w : Nat → Nat) (A B : Nat → Bool)
    (h : ∀ i, i < n → A i = true → B i = false) :
    mass n w (fun i => A i || B i) = mass n w A + mass n w B := by
  rw [mass, mass, mass, ← nsum_add]
  apply nsum_congr
  intro i hi
  cases ha : A i with
  | false => simp [eventWeight, ha]
  | true => simp [eventWeight, ha, h i hi ha]

theorem intersection_comm (n : Nat) (w : Nat → Nat) (A B : Nat → Bool) :
    mass n w (fun i => A i && B i) = mass n w (fun i => B i && A i) := by
  apply nsum_congr
  intro i _
  cases ha : A i <;> cases hb : B i <;> simp [eventWeight, ha, hb]

/-- A bounded union; no countable union or infinite search is hidden here. -/
def unionBelow : Nat → (Nat → Nat → Bool) → Nat → Bool
  | 0, _, _ => false
  | k + 1, A, i => unionBelow k A i || A k i

theorem finite_union_bound (n k : Nat) (w : Nat → Nat) (A : Nat → Nat → Bool) :
    mass n w (unionBelow k A) ≤ nsum k (fun j => mass n w (A j)) := by
  induction k with
  | zero => simp [unionBelow, nsum]
  | succ k ih =>
    exact Nat.le_trans (union_bound n w (unionBelow k A) (A k))
      (Nat.add_le_add_right ih (mass n w (A k)))

/-- The integer numerator of the expectation of a nonnegative observable. -/
def moment (n : Nat) (w x : Nat → Nat) : Nat :=
  nsum n (fun i => w i * x i)

theorem moment_add (n : Nat) (w x y : Nat → Nat) :
    moment n w (fun i => x i + y i) = moment n w x + moment n w y := by
  simp only [moment, Nat.mul_add, nsum_add]

theorem moment_mono (n : Nat) (w x y : Nat → Nat)
    (h : ∀ i, i < n → x i ≤ y i) : moment n w x ≤ moment n w y := by
  apply nsum_mono
  intro i hi
  exact Nat.mul_le_mul_left (w i) (h i hi)

/-- Markov's inequality for any event on which `x ≥ t`, with denominators cleared. -/
theorem markov_event (n t : Nat) (w x : Nat → Nat) (A : Nat → Bool)
    (h : ∀ i, i < n → A i = true → t ≤ x i) :
    t * mass n w A ≤ moment n w x := by
  rw [mass, ← nsum_mul_left]
  apply nsum_mono
  intro i hi
  cases ha : A i with
  | false => simp [eventWeight, ha]
  | true =>
    simp only [eventWeight, ha, Bool.true_eq, ↓reduceIte]
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (w i) (h i hi ha)

theorem markov (n t : Nat) (w x : Nat → Nat) :
    t * mass n w (fun i => decide (t ≤ x i)) ≤ moment n w x := by
  apply markov_event
  intro i _ hi
  exact of_decide_eq_true hi

/-- Unsigned difference, avoiding any implicit conversion to real numbers. -/
def absDiff (a b : Nat) : Nat := (a - b) + (b - a)

/-- Event probabilities are stable in symmetric-difference distance. -/
theorem event_mass_stability (n : Nat) (w : Nat → Nat) (A B : Nat → Bool) :
    absDiff (mass n w A) (mass n w B) ≤
      mass n w (fun i => xor (A i) (B i)) := by
  have hAB : mass n w A ≤ mass n w B + mass n w (fun i => xor (A i) (B i)) := by
    rw [mass, mass, mass, ← nsum_add]
    apply nsum_mono
    intro i _
    cases ha : A i <;> cases hb : B i <;> simp [eventWeight, ha, hb]
  have hBA : mass n w B ≤ mass n w A + mass n w (fun i => xor (A i) (B i)) := by
    rw [mass, mass, mass, ← nsum_add]
    apply nsum_mono
    intro i _
    cases ha : A i <;> cases hb : B i <;> simp [eventWeight, ha, hb]
  unfold absDiff
  omega

/-- A second-moment numerator around the scaled rational centre `a/d`.
`d` is a natural scale.  The finite inequality itself does not need `d > 0`.
-/
def centeredSecond (n a d : Nat) (w x : Nat → Nat) : Nat :=
  moment n w (fun i => absDiff (d * x i) a ^ 2)

/-- A denominator-cleared Chebyshev inequality, valid at any centre.
For `d > 0`, the event means `|x - a/d| ≥ t/d`.
-/
theorem chebyshev (n a d t : Nat) (w x : Nat → Nat) :
    t ^ 2 * mass n w (fun i => decide (t ≤ absDiff (d * x i) a)) ≤
      centeredSecond n a d w x := by
  apply markov_event
  intro i _ hi
  exact Nat.pow_le_pow_left (of_decide_eq_true hi) 2

/-- Rectangular product-event mass on a finite product space. -/
def rectangleMass (n m : Nat) (w v : Nat → Nat) (A B : Nat → Bool) : Nat :=
  nsum n (fun i => nsum m (fun j => eventWeight w A i * eventWeight v B j))

theorem product_rectangle (n m : Nat) (w v : Nat → Nat) (A B : Nat → Bool) :
    rectangleMass n m w v A B = mass n w A * mass m v B := by
  exact nsum_product n m (eventWeight w A) (eventWeight v B)

theorem product_weight_is_intersection (w v : Nat → Nat)
    (A B : Nat → Bool) (i j : Nat) :
    eventWeight w A i * eventWeight v B j =
      (if A i && B j then w i * v j else 0) := by
  cases ha : A i <;> cases hb : B j <;> simp [eventWeight, ha, hb]

/-- Finite laws require positive total weight; normalization is rational division. -/
structure FiniteLaw where
  size : Nat
  weight : Nat → Nat
  positive : 0 < nsum size weight

/-- Concrete smoke checks; the general theorems above do not rely on these examples. -/
example : mass 4 (fun _ => 1) (fun i => decide (i < 2)) = 2 := by decide
example : moment 4 (fun _ => 1) (fun i => i) = 6 := by decide
example : rectangleMass 2 3 (fun _ => 1) (fun _ => 1)
    (fun _ => true) (fun _ => true) = 6 := by decide

end IPRAProbability
