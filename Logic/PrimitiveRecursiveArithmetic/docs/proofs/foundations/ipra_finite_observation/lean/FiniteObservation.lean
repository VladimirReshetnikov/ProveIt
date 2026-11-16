import Std

/-!
# Finite-observation kernels

These are ambient Lean proofs of finite, constructive lemmas. They are not
object-language iPRA derivations. `iter` deliberately supplies a semantic
reference using function-valued recursion; `build` computes finite tables.
The manuscript proves why the latter has a first-order PR implementation.
No evaluator of arbitrary PR program codes is assumed.
-/

namespace FiniteObservation

abbrev Stream := Nat → Nat
abbrev Table := List Nat

def PrefixEq (h : Nat) (a b : Stream) : Prop := ∀ i, i ≤ h → a i = b i

def lookup (xs : Table) : Stream := fun i => xs[i]?.getD 0

def tabulate (a : Stream) (h : Nat) : Table := (List.range (h + 1)).map a

@[simp] theorem lookup_tabulate (a : Stream) {h i : Nat} (hi : i ≤ h) :
    lookup (tabulate a h) i = a i := by
  simp [lookup, tabulate, Nat.lt_succ_iff.mpr hi]

/-- A numerical iteration of a fixed demand function. -/
def demand (u : Nat → Nat) : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => u (demand u n k)

theorem demand_commute (u : Nat → Nat) (n k : Nat) :
    demand u n (u k) = u (demand u n k) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [demand, ih]

/-- A stage's outputs through k depend only on input observations through u k. -/
def Local (u : Nat → Nat) (t : Nat → Stream → Stream) : Prop :=
  ∀ s k a b, PrefixEq (u k) a b → PrefixEq k (t s a) (t s b)

theorem tabulate_congr {a b : Stream} {h : Nat} (hab : PrefixEq h a b) :
    tabulate a h = tabulate b h := by
  apply List.map_congr_left
  intro i hi
  apply hab i
  have : i < h + 1 := List.mem_range.mp hi
  omega

/-- A transformer expressed solely through a finite numerical table body. -/
def ofBody (u : Nat → Nat) (body : Nat → Nat → Table → Nat)
    (s : Nat) (a : Stream) (p : Nat) : Nat := body s p (tabulate a (u p))

theorem ofBody_local (u : Nat → Nat) (body : Nat → Nat → Table → Nat)
    (hu : ∀ p k, p ≤ k → u p ≤ u k) : Local u (ofBody u body) := by
  intro s k a b hab p hp
  unfold ofBody
  apply congrArg (body s p)
  apply tabulate_congr
  intro i hi
  exact hab i (Nat.le_trans hi (hu p k hp))

def iter (t : Nat → Stream → Stream) (a : Stream) : Nat → Stream
  | 0 => a
  | n + 1 => t n (iter t a n)

/-- Iteration needs only a primitive-recursively growing finite prefix. -/
theorem iter_local {u : Nat → Nat} {t : Nat → Stream → Stream}
    (ht : Local u t) (n k : Nat) {a b : Stream}
    (h : PrefixEq (demand u n k) a b) :
    PrefixEq k (iter t a n) (iter t b n) := by
  induction n generalizing k with
  | zero => exact h
  | succ n ih =>
    apply ht n k
    apply ih (u k)
    simpa only [demand, demand_commute] using h

/-- Precision available at stage s of an N-stage construction. -/
def horizon (u : Nat → Nat) (N k s : Nat) : Nat := demand u (N - s) k

theorem horizon_step (u : Nat → Nat) {N k s : Nat} (hs : s < N) :
    horizon u N k s = u (horizon u N k (s + 1)) := by
  have hn : N - s = (N - (s + 1)) + 1 := by omega
  simp only [horizon, hn, demand]

/-- The actual implementation stores a finite table at every stage.
    Parameters N and k stay fixed during this natural-number recursion. -/
def build (u : Nat → Nat) (t : Nat → Stream → Stream)
    (a : Stream) (N k : Nat) : Nat → Table
  | 0 => tabulate a (horizon u N k 0)
  | s + 1 => tabulate (t s (lookup (build u t a N k s)))
      (horizon u N k (s + 1))

/-- Numerical table compilation agrees with the semantic nested construction. -/
theorem build_correct {u : Nat → Nat} {t : Nat → Stream → Stream}
    (ht : Local u t) (a : Stream) (N k s : Nat) (hs : s ≤ N) :
    PrefixEq (horizon u N k s) (lookup (build u t a N k s)) (iter t a s) := by
  induction s with
  | zero =>
    intro i hi
    exact lookup_tabulate a hi
  | succ s ih =>
    have hsn : s < N := by omega
    have hb := ih (by omega)
    have hinput : PrefixEq (u (horizon u N k (s + 1)))
        (lookup (build u t a N k s)) (iter t a s) := by
      rw [← horizon_step u hsn]
      exact hb
    have hout := ht s (horizon u N k (s + 1)) _ _ hinput
    intro i hi
    change lookup (tabulate (t s (lookup (build u t a N k s)))
      (horizon u N k (s + 1))) i = t s (iter t a s) i
    rw [lookup_tabulate _ hi]
    exact hout i hi

/-- End-to-end form: only finite tables occur in the executable side. -/
theorem compiled_correct {u : Nat → Nat} {t : Nat → Stream → Stream}
    (ht : Local u t) (a : Stream) (N k : Nat) :
    lookup (build u t a N k N) k = iter t a N k := by
  have h := build_correct ht a N k N (Nat.le_refl N)
  exact h k (by simp [horizon, demand])

/-- A bounded Boolean conjunction and its exact reflection theorem. -/
def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => allBelow p n && p n

theorem allBelow_iff (p : Nat → Bool) (n : Nat) :
    allBelow p n = true ↔ ∀ i, i < n → p i = true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true, ih]
    constructor
    · intro h i hi
      by_cases he : i = n
      · simpa [he] using h.2
      · exact h.1 i (by omega)
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

/-- Safety on a finite horizon under a fixed Boolean invariant. -/
def run (step : Nat → Nat → Nat) (start : Nat) : Nat → Nat
  | 0 => start
  | n + 1 => step n (run step start n)

theorem finite_safety (step : Nat → Nat → Nat) (start H : Nat)
    (inv : Nat → Nat → Bool) (h0 : inv 0 start = true)
    (hstep : ∀ j s, j < H → inv j s = true → inv (j + 1) (step j s) = true) :
    ∀ j, j ≤ H → inv j (run step start j) = true := by
  intro j
  induction j with
  | zero => intro _; exact h0
  | succ j ih =>
    intro hj
    exact hstep j (run step start j) (by omega) (ih (by omega))

/-- Scalar strict descent is bounded by its initial natural rank. -/
theorem descent_fuel (rank : Nat → Nat) (H : Nat)
    (hstep : ∀ j, j < H → rank (j + 1) < rank j) : H ≤ rank 0 := by
  have h : ∀ j, j ≤ H → rank j + j ≤ rank 0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have hr := hstep j (by omega)
      have hp := ih (by omega)
      omega
  have := h H (Nat.le_refl H)
  omega

end FiniteObservation

#print axioms FiniteObservation.compiled_correct
#print axioms FiniteObservation.allBelow_iff
#print axioms FiniteObservation.finite_safety
#print axioms FiniteObservation.descent_fuel
