import Std

/-!
# Cleared affine recurrence bounds

This file is checked in the Lean metatheory.  It is NOT by itself an object-level
derivation in iPRA.  The companion adapter and report explain the translation:
the displayed invariant is quantifier-free after natural-number coding, and the
recurrences are primitive recursive. No `sorry`, added axiom, or classical choice
is used here.
-/

namespace IPRACoupled

set_option linter.unusedSimpArgs false

/-- The homogeneous denominator-cleared geometric sum. -/
def geom (c d : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => c * geom c d n + d ^ n

/-- Numerator bound for a recurrence with a time-dependent forcing term. -/
def envelope (c d initial : Nat) (forcing : Nat → Nat) : Nat → Nat
  | 0 => initial
  | n + 1 => c * envelope c d initial forcing n + d ^ n * forcing n

theorem scaled_envelope (c d : Nat) (a forcing : Nat → Nat)
    (step : ∀ n, d * a (n + 1) ≤ c * a n + forcing n) :
    ∀ n, d ^ n * a n ≤ envelope c d (a 0) forcing n := by
  intro n
  induction n with
  | zero => simp [envelope]
  | succ n ih =>
    calc
      d ^ (n + 1) * a (n + 1) = d ^ n * (d * a (n + 1)) := by
        simp [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ d ^ n * (c * a n + forcing n) := Nat.mul_le_mul_left _ (step n)
      _ = c * (d ^ n * a n) + d ^ n * forcing n := by
        simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ c * envelope c d (a 0) forcing n + d ^ n * forcing n :=
        Nat.add_le_add_right (Nat.mul_le_mul_left c ih) _
      _ = envelope c d (a 0) forcing (n + 1) := rfl

theorem envelope_constant (c d initial r : Nat) :
    ∀ n, envelope c d initial (fun _ => r) n =
      c ^ n * initial + r * geom c d n := by
  intro n
  induction n with
  | zero => simp [envelope, geom]
  | succ n ih =>
    simp only [envelope, ih, geom, Nat.pow_succ, Nat.mul_add]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem scaled_affine_bound (c d r : Nat) (a : Nat → Nat)
    (step : ∀ n, d * a (n + 1) ≤ c * a n + r) (n : Nat) :
    d ^ n * a n ≤ c ^ n * a 0 + r * geom c d n := by
  simpa only [envelope_constant] using
    scaled_envelope c d a (fun _ => r) step n

/-- For denominator one larger than the numerator, the geometric sum telescopes.
The equality uses no subtraction and is suitable as a QF invariant. -/
theorem geom_complement (c : Nat) :
    ∀ n, geom c (c + 1) n + c ^ n = (c + 1) ^ n := by
  intro n
  induction n with
  | zero => simp [geom]
  | succ n ih =>
    calc
      geom c (c + 1) (n + 1) + c ^ (n + 1) =
          c * (geom c (c + 1) n + c ^ n) + (c + 1) ^ n := by
        simp [geom, Nat.pow_succ, Nat.mul_add, Nat.mul_comm,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ = c * (c + 1) ^ n + (c + 1) ^ n := by rw [ih]
      _ = (c + 1) ^ (n + 1) := by
        simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_comm]

/-- Exact denominator-cleared affine contraction estimate. -/
theorem affine_contraction_bound (c r : Nat) (a : Nat → Nat)
    (step : ∀ n, (c + 1) * a (n + 1) ≤ c * a n + r) (n : Nat) :
    (c + 1) ^ n * a n + r * c ^ n ≤
      c ^ n * a 0 + r * (c + 1) ^ n := by
  have h := Nat.add_le_add_right (scaled_affine_bound c (c + 1) r a step n) (r * c ^ n)
  have he : c ^ n * a 0 + r * geom c (c + 1) n + r * c ^ n =
      c ^ n * a 0 + r * (c + 1) ^ n := by
    rw [Nat.add_assoc, ← Nat.mul_add, geom_complement]
  rw [he] at h
  exact h

/-- A finite, checkable budget turns the affine estimate into a target bound. -/
theorem affine_budget (c r target : Nat) (a : Nat → Nat)
    (step : ∀ n, (c + 1) * a (n + 1) ≤ c * a n + r) (n : Nat)
    (budget : c ^ n * a 0 + r * (c + 1) ^ n ≤
      (c + 1) ^ n * target + r * c ^ n) : a n ≤ target := by
  have h := Nat.le_trans (affine_contraction_bound c r a step n) budget
  have hm : (c + 1) ^ n * a n ≤ (c + 1) ^ n * target :=
    Nat.le_of_add_le_add_right h
  have hp : 0 < (c + 1) ^ n := Nat.pow_pos (by omega)
  exact Nat.le_of_mul_le_mul_left hm hp

/-- A bounded sum, written explicitly to keep its primitive recursion visible. -/
def nsum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => nsum f n + f n

theorem nsum_mono {f g : Nat → Nat} {N : Nat}
    (h : ∀ j, j < N → f j ≤ g j) : nsum f N ≤ nsum g N := by
  induction N with
  | zero => simp [nsum]
  | succ N ih =>
    exact Nat.add_le_add (ih (fun j hj => h j (by omega))) (h N (by omega))

theorem nsum_mul_left (a N : Nat) (f : Nat → Nat) :
    nsum (fun j => a * f j) N = a * nsum f N := by
  induction N with
  | zero => simp [nsum]
  | succ N ih => simp [nsum, ih, Nat.mul_add]

theorem nsum_mul_right (a N : Nat) (f : Nat → Nat) :
    nsum (fun j => f j * a) N = nsum f N * a := by
  simpa only [Nat.mul_comm] using nsum_mul_left a N f

/-- A finite nonnegative matrix is dominated by one scalar in a weighted norm.
No division by a weight occurs in this denominator-cleared statement. -/
theorem weighted_row (N c wi E : Nat) (row weights errors : Nat → Nat)
    (herr : ∀ j, j < N → errors j ≤ weights j * E)
    (hrow : nsum (fun j => row j * weights j) N ≤ c * wi) :
    nsum (fun j => row j * errors j) N ≤ wi * (c * E) := by
  calc
    nsum (fun j => row j * errors j) N ≤
        nsum (fun j => (row j * weights j) * E) N := by
      apply nsum_mono
      intro j hj
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (row j) (herr j hj)
    _ = nsum (fun j => row j * weights j) N * E := nsum_mul_right _ _ _
    _ ≤ (c * wi) * E := Nat.mul_le_mul_right E hrow
    _ = wi * (c * E) := by ac_rfl

/-- Coupled perturbation estimate with an explicit weighted-row certificate.
The matrix and forcing may be arbitrary host functions here; an iPRA application
uses fixed PR bodies, with N and all other inputs coded as natural parameters. -/
theorem coupled_envelope (N c d initial : Nat)
    (matrix : Nat → Nat → Nat) (weights forcing : Nat → Nat)
    (errors : Nat → Nat → Nat)
    (base : ∀ i, i < N → errors 0 i ≤ weights i * initial)
    (rows : ∀ i, i < N →
      nsum (fun j => matrix i j * weights j) N ≤ c * weights i)
    (step : ∀ n i, i < N → d * errors (n + 1) i ≤
      nsum (fun j => matrix i j * errors n j) N + weights i * forcing n) :
    ∀ n i, i < N → d ^ n * errors n i ≤
      weights i * envelope c d initial forcing n := by
  intro n
  induction n with
  | zero => simpa only [Nat.pow_zero, Nat.one_mul, envelope] using base
  | succ n ih =>
    intro i hi
    have hr := weighted_row N c (weights i) (envelope c d initial forcing n)
      (matrix i) weights (fun j => d ^ n * errors n j) ih (rows i hi)
    calc
      d ^ (n + 1) * errors (n + 1) i = d ^ n * (d * errors (n + 1) i) := by
        simp [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ d ^ n *
          (nsum (fun j => matrix i j * errors n j) N + weights i * forcing n) :=
        Nat.mul_le_mul_left _ (step n i hi)
      _ = nsum (fun j => matrix i j * (d ^ n * errors n j)) N +
          weights i * (d ^ n * forcing n) := by
        rw [Nat.mul_add, ← nsum_mul_left]
        congr 1
        · congr 1; funext j; ac_rfl
        · ac_rfl
      _ ≤ weights i * (c * envelope c d initial forcing n) +
          weights i * (d ^ n * forcing n) := Nat.add_le_add_right hr _
      _ = weights i * envelope c d initial forcing (n + 1) := by
        rw [envelope, Nat.mul_add]

/-- The exact closed form for the coupled estimate when d = c+1. -/
theorem coupled_contraction_bound (N c initial r : Nat)
    (matrix : Nat → Nat → Nat) (weights : Nat → Nat)
    (errors : Nat → Nat → Nat)
    (base : ∀ i, i < N → errors 0 i ≤ weights i * initial)
    (rows : ∀ i, i < N →
      nsum (fun j => matrix i j * weights j) N ≤ c * weights i)
    (step : ∀ n i, i < N → (c + 1) * errors (n + 1) i ≤
      nsum (fun j => matrix i j * errors n j) N + weights i * r)
    (n i : Nat) (hi : i < N) :
    (c + 1) ^ n * errors n i + weights i * (r * c ^ n) ≤
      weights i * (c ^ n * initial + r * (c + 1) ^ n) := by
  have h := coupled_envelope N c (c + 1) initial matrix weights
    (fun _ => r) errors base rows step n i hi
  rw [envelope_constant] at h
  have hh := Nat.add_le_add_right h (weights i * (r * c ^ n))
  have he : weights i * (c ^ n * initial + r * geom c (c + 1) n) +
      weights i * (r * c ^ n) =
      weights i * (c ^ n * initial + r * (c + 1) ^ n) := by
    rw [← Nat.mul_add, Nat.add_assoc, ← Nat.mul_add, geom_complement]
  rw [he] at hh
  exact hh

/-- A denominator-cleared Bernoulli bound, using one explicit positive term. -/
theorem bernoulli_clear (c : Nat) : ∀ n,
    c ^ (n + 1) + (n + 1) * c ^ n ≤ (c + 1) ^ (n + 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h := Nat.mul_le_mul_right (c + 1) ih
    have he : (c ^ (n + 1) + (n + 1) * c ^ n) * (c + 1) =
        (c ^ (n + 2) + (n + 2) * c ^ (n + 1)) + (n + 1) * c ^ n := by
      simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_two, Nat.two_mul, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [he, ← Nat.pow_succ] at h
    exact Nat.le_trans (Nat.le_add_right _ _) h

/-- After c+1 steps, the rational contraction c/(c+1) has shrunk by at least 1/2. -/
theorem block_halving (c : Nat) : 2 * c ^ (c + 1) ≤ (c + 1) ^ (c + 1) := by
  have h := bernoulli_clear c c
  have hh : 2 * c ^ (c + 1) ≤ c ^ (c + 1) + (c + 1) * c ^ c := by
    have hc : c ^ (c + 1) ≤ (c + 1) * c ^ c := by
      rw [Nat.pow_succ]
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (c ^ c) (Nat.le_succ c)
    simpa only [Nat.two_mul] using Nat.add_le_add_left hc (c ^ (c + 1))
  exact Nat.le_trans hh h

/-- An entirely elementary primitive-recursive convergence clock. -/
theorem geometric_clock (c : Nat) : ∀ m,
    2 ^ m * c ^ ((c + 1) * m) ≤ (c + 1) ^ ((c + 1) * m) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have h := Nat.mul_le_mul ih (block_halving c)
    simpa [Nat.mul_add, Nat.pow_add, Nat.pow_succ, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm] using h

/-- Remove the recurrent part from a residual inequality without division. -/
theorem residual_separation {d c v r : Nat} (hc : c ≤ d)
    (h : d * v ≤ c * v + r) : (d - c) * v ≤ r := by
  have he : (d - c) * v + c * v = d * v := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hc]
  omega

/-- Explicit two-component elimination. The determinant gap is data; proving
its positivity yields a quantitative a-posteriori bound by division outside
this cleared inequality. No existence theorem for a matrix inverse is used. -/
theorem two_component_residual {A B b c x y r s : Nat}
    (hx : A * x ≤ b * y + r) (hy : B * y ≤ c * x + s)
    (hgap : b * c ≤ A * B) :
    (A * B - b * c) * x ≤ B * r + b * s := by
  have hh : (A * B) * x ≤ (b * c) * x + (B * r + b * s) := by
    calc
      (A * B) * x = B * (A * x) := by ac_rfl
      _ ≤ B * (b * y + r) := Nat.mul_le_mul_left B hx
      _ = b * (B * y) + B * r := by
        simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ b * (c * x + s) + B * r :=
        Nat.add_le_add_right (Nat.mul_le_mul_left b hy) _
      _ = (b * c) * x + (B * r + b * s) := by
        simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  exact residual_separation hgap hh

/-- Finite telescoping of successive error budgets. -/
theorem finite_telescope (a increments : Nat → Nat)
    (step : ∀ n, a (n + 1) ≤ a n + increments n) :
    ∀ n, a n ≤ a 0 + nsum increments n := by
  intro n
  induction n with
  | zero => simp [nsum]
  | succ n ih =>
    have h := Nat.le_trans (step n) (Nat.add_le_add_right ih (increments n))
    simpa only [nsum, Nat.add_assoc] using h

#print axioms scaled_envelope
#print axioms envelope_constant
#print axioms scaled_affine_bound
#print axioms geom_complement
#print axioms affine_contraction_bound
#print axioms affine_budget
#print axioms nsum_mono
#print axioms nsum_mul_left
#print axioms nsum_mul_right
#print axioms weighted_row
#print axioms coupled_envelope
#print axioms coupled_contraction_bound
#print axioms bernoulli_clear
#print axioms block_halving
#print axioms geometric_clock
#print axioms residual_separation
#print axioms two_component_residual
#print axioms finite_telescope

end IPRACoupled
