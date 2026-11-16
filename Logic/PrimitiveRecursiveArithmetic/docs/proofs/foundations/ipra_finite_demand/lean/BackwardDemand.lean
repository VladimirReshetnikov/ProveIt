import Std

/-!
# Backward demands for finite observations

Checked with Lean 4.32.0; only `Std` is imported.

The statements in this file are semantic Lean theorems.  Their proofs explicitly
use a fixed terminal horizon and a finite schedule.  They are NOT declarations
of object-theory `Prf PRAAx` derivations.  The accompanying article describes the
separate syntactic translation: the demand functions must have fixed PR syntax,
the predicates must be bounded/Booleanized, and base and step contracts must be
supplied as object-iPRA derivations.  There is no evaluator for arbitrary PR code.
-/

namespace FiniteDemand

/-- Build a demand backwards from terminal time `N` and terminal demand `k`.
For `j ≤ N`, `j` counts how many predecessor steps have been traversed. -/
def backward (D : Nat → Nat → Nat) (N k : Nat) : Nat → Nat
  | 0 => k
  | j + 1 => D (N - (j + 1)) (backward D N k j)

/-- The observation demanded at forward time `t`.
The useful contract is restricted to `t ≤ N`. -/
def horizon (D : Nat → Nat → Nat) (N k t : Nat) : Nat :=
  backward D N k (N - t)

@[simp] theorem horizon_final (D : Nat → Nat → Nat) (N k : Nat) :
    horizon D N k N = k := by
  simp [horizon, backward]

theorem horizon_step (D : Nat → Nat → Nat) (N k t : Nat) (ht : t < N) :
    horizon D N k t = D t (horizon D N k (t + 1)) := by
  have hsub : N - t = (N - (t + 1)) + 1 := by omega
  have htime : N - ((N - (t + 1)) + 1) = t := by omega
  simp only [horizon]
  rw [hsub, backward, htime]

theorem backward_coherence (D : Nat → Nat → Nat) (N k j : Nat) :
    backward D (N + 1) k (j + 1) = backward D N (D N k) j := by
  induction j with
  | zero => simp [backward]
  | succ j ih =>
      change D (N + 1 - (j + 1 + 1)) (backward D (N + 1) k (j + 1)) =
        D (N - (j + 1)) (backward D N (D N k) j)
      rw [ih]
      have htime : N + 1 - (j + 1 + 1) = N - (j + 1) := by omega
      rw [htime]

theorem horizon_coherence (D : Nat → Nat → Nat) (N k t : Nat) (ht : t ≤ N) :
    horizon D (N + 1) k t = horizon D N (D N k) t := by
  have hsub : N + 1 - t = (N - t) + 1 := by omega
  simp only [horizon]
  rw [hsub, backward_coherence]

/-- Forward primitive recursion after the demand schedule is known. -/
def advance (F : Nat → Nat → Nat → Nat) (H : Nat → Nat)
    (initial : Nat) : Nat → Nat
  | 0 => initial
  | t + 1 => F t (H (t + 1)) (advance F H initial t)

theorem advance_congr (F : Nat → Nat → Nat → Nat)
    (H K : Nat → Nat) (u v n : Nat) (huv : u = v)
    (hHK : ∀ t, t ≤ n → H t = K t) :
    advance F H u n = advance F K v n := by
  induction n with
  | zero => exact huv
  | succ n ih =>
      simp only [advance]
      rw [hHK (n + 1) (Nat.le_refl _)]
      rw [ih (fun t ht => hHK t (by omega))]

/-- A parameter-changing recursion compiled into two ordinary recursions.
For fixed PR `D`, `b`, and `F`, this expression has fixed PR syntax.
The PR syntax and object-theory proof compiler are not implemented here. -/
def compiledRecursion (D : Nat → Nat → Nat) (b : Nat → Nat)
    (F : Nat → Nat → Nat → Nat) (N k : Nat) : Nat :=
  advance F (horizon D N k) (b (horizon D N k 0)) N

@[simp] theorem compiledRecursion_zero
    (D : Nat → Nat → Nat) (b : Nat → Nat) (F : Nat → Nat → Nat → Nat)
    (k : Nat) : compiledRecursion D b F 0 k = b k := by
  simp [compiledRecursion, advance]

theorem compiledRecursion_succ
    (D : Nat → Nat → Nat) (b : Nat → Nat) (F : Nat → Nat → Nat → Nat)
    (N k : Nat) :
    compiledRecursion D b F (N + 1) k =
      F N k (compiledRecursion D b F N (D N k)) := by
  simp only [compiledRecursion, advance, horizon_final]
  congr 1
  apply advance_congr
  · rw [horizon_coherence D N k 0 (Nat.zero_le N)]
  · exact fun t ht => horizon_coherence D N k t ht

/-- The finite transfer theorem: a *single* initial observation suffices.
No monotonicity hypothesis on `D` or `P` is used. -/
theorem transfer (P : Nat → Nat → Prop) (D : Nat → Nat → Nat)
    (N k : Nat)
    (base : P 0 (horizon D N k 0))
    (step : ∀ n r, n < N → P n (D n r) → P (n + 1) r) :
    P N k := by
  have finiteInvariant : ∀ t, t ≤ N → P t (horizon D N k t) := by
    intro t
    induction t with
    | zero =>
        intro _
        exact base
    | succ t ih =>
        intro ht
        have hlt : t < N := by omega
        have hp := ih (by omega)
        rw [horizon_step D N k t hlt] at hp
        exact step t (horizon D N k (t + 1)) hlt hp
  simpa using finiteInvariant N (Nat.le_refl N)

/-- Universal closure after the finite transfer.  The accompanying arithmetic
metatheorem applies only to bounded `P`, PR `D`, and supplied object proofs. -/
theorem observational_induction (P : Nat → Nat → Prop)
    (D : Nat → Nat → Nat)
    (base : ∀ k, P 0 k)
    (step : ∀ n k, P n (D n k) → P (n + 1) k) :
    ∀ N k, P N k := by
  intro N k
  apply transfer P D N k
  · exact base _
  · intro n r _ hp
    exact step n r hp

/-- Maximum of the values `f 0, ..., f (m-1)`, with empty maximum zero. -/
def prefixMax (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => max (prefixMax f m) (f m)

theorem le_prefixMax (f : Nat → Nat) (m i : Nat) (hi : i < m) :
    f i ≤ prefixMax f m := by
  induction m with
  | zero => omega
  | succ m ih =>
      simp only [prefixMax]
      by_cases h : i < m
      · exact Nat.le_trans (ih h) (Nat.le_max_left _ _)
      · have heq : i = m := by omega
        subst i
        exact Nat.le_max_right _ _

/-- A finite list of predecessor queries for every output query.
`count n j` is its length and `query n j r` its `r`th element.
The envelope covers every output observation `j ≤ h`; neither function need
be monotone in any argument. -/
def envelope (count : Nat → Nat → Nat) (query : Nat → Nat → Nat → Nat)
    (n h : Nat) : Nat :=
  prefixMax (fun j => prefixMax (query n j) (count n j)) (h + 1)

theorem query_le_envelope
    (count : Nat → Nat → Nat) (query : Nat → Nat → Nat → Nat)
    (n h j r : Nat) (hj : j ≤ h) (hr : r < count n j) :
    query n j r ≤ envelope count query n h := by
  exact Nat.le_trans
    (le_prefixMax (query n j) (count n j) r hr)
    (le_prefixMax (fun j => prefixMax (query n j) (count n j))
      (h + 1) j (by omega))

/-- Observations can require a variable finite list of predecessor facts.
The proof reduces them to bounded prefix observations before using `transfer`.
This is the reusable semantic theorem behind the finite-demand graph form. -/
theorem finite_query_induction (A : Nat → Nat → Prop)
    (count : Nat → Nat → Nat) (query : Nat → Nat → Nat → Nat)
    (base : ∀ j, A 0 j)
    (step : ∀ n j, (∀ r, r < count n j → A n (query n j r)) → A (n + 1) j) :
    ∀ N j, A N j := by
  let P : Nat → Nat → Prop := fun n h => ∀ j, j ≤ h → A n j
  have bp : ∀ h, P 0 h := by
    intro h j _
    exact base j
  have sp : ∀ n h, P n (envelope count query n h) → P (n + 1) h := by
    intro n h hp j hj
    apply step n j
    intro r hr
    exact hp _ (query_le_envelope count query n h j r hj hr)
  intro N j
  exact observational_induction P (envelope count query) bp sp N j j (Nat.le_refl j)

/-- Constant precision cost has an explicit accumulated horizon. -/
theorem backward_constant_shift (c N k j : Nat) :
    backward (fun _ r => r + c) N k j = k + j * c := by
  induction j with
  | zero => simp [backward]
  | succ j ih => simp [backward, ih, Nat.succ_mul, Nat.add_assoc]

theorem horizon_constant_shift (c N k t : Nat) :
    horizon (fun _ r => r + c) N k t = k + (N - t) * c := by
  exact backward_constant_shift c N k (N - t)

/-- A simple specialization used by repeated Lipschitz arithmetic. -/
theorem constant_shift_transfer (P : Nat → Nat → Prop) (c N k : Nat)
    (base : P 0 (k + N * c))
    (step : ∀ n r, n < N → P n (r + c) → P (n + 1) r) :
    P N k := by
  apply transfer P (fun _ r => r + c) N k
  · simpa [horizon_constant_shift] using base
  · exact step

#eval horizon (fun n k => k + n + 1) 4 3 0
#eval horizon (fun _ k => k + 2) 5 7 0

#print axioms horizon_step
#print axioms compiledRecursion_succ
#print axioms transfer
#print axioms observational_induction
#print axioms finite_query_induction
#print axioms constant_shift_transfer

end FiniteDemand
