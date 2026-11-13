import Std

/-!
# Fresh names reserved on successful return

This file formalizes only the name-allocation bookkeeping of a finite
successful checker call tree.  It does not formalize Python evaluation,
certificate decoding, any arithmetic calculus, or the iPRA interpretation.

The natural clock is the negative of the checker's global floor.  A leaf
returns after advancing the clock once.  An internal call checks its major
subtree, uses that subtree's return clock as its fresh name, checks its
continuation, and advances once more before its own return.

No axioms or `sorry` declarations are introduced.
-/

namespace FreshReturn

inductive Trace where
  | leaf
  | node (major continuation : Trace)
  deriving Repr, DecidableEq

/-- Number of successful calls, including leaves and the outermost call. -/
def nodeCount : Trace → Nat
  | .leaf => 1
  | .node major continuation => nodeCount major + nodeCount continuation + 1

/-- Clock immediately after the call has returned successfully. -/
def finish : Trace → Nat → Nat
  | .leaf, start => start + 1
  | .node major continuation, start =>
      finish continuation (finish major start) + 1

/-- Names actually consumed at inference nodes, in execution order. -/
def allocations : Trace → Nat → List Nat
  | .leaf, _ => []
  | .node major continuation, start =>
      allocations major start ++
        finish major start :: allocations continuation (finish major start)

/-- Clocks at which the modeled scope-sensitive operations may be checked.
Duplicated clocks are harmless; final return reservations are excluded. -/
def checkClocks : Trace → Nat → List Nat
  | .leaf, start => [start]
  | .node major continuation, start =>
      start :: (checkClocks major start ++
        finish major start :: checkClocks continuation (finish major start))

theorem nodeCount_pos (t : Trace) : 0 < nodeCount t := by
  cases t <;> simp [nodeCount]

theorem finish_eq (t : Trace) (start : Nat) :
    finish t start = start + nodeCount t := by
  induction t generalizing start with
  | leaf => rfl
  | node major continuation ihMajor ihContinuation =>
      simp [finish, nodeCount, ihMajor, ihContinuation, Nat.add_assoc]

theorem finish_strict (t : Trace) (start : Nat) : start < finish t start := by
  rw [finish_eq]
  have h := nodeCount_pos t
  omega

theorem allocation_bounds (t : Trace) (start name : Nat)
    (h : name ∈ allocations t start) :
    start < name ∧ name < finish t start := by
  induction t generalizing start with
  | leaf => simp [allocations] at h
  | node major continuation ihMajor ihContinuation =>
      simp only [allocations, List.mem_append, List.mem_cons] at h
      have hMajorEnd := finish_strict major start
      have hContinuationEnd := finish_strict continuation (finish major start)
      simp only [finish]
      rcases h with hMajor | hRoot | hContinuation
      · have hb := ihMajor start hMajor
        exact ⟨hb.1, Nat.lt_trans hb.2
          (Nat.lt_trans hContinuationEnd (Nat.lt_succ_self _))⟩
      · subst name
        exact ⟨hMajorEnd, Nat.lt_trans hContinuationEnd (Nat.lt_succ_self _)⟩
      · have hb := ihContinuation (finish major start) hContinuation
        exact ⟨Nat.lt_trans hMajorEnd hb.1,
          Nat.lt_trans hb.2 (Nat.lt_succ_self _)⟩

theorem checkClock_bounds (t : Trace) (start clock : Nat)
    (h : clock ∈ checkClocks t start) :
    start ≤ clock ∧ clock < finish t start := by
  induction t generalizing start with
  | leaf =>
      simp only [checkClocks, List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [finish]
      subst clock
      exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
  | node major continuation ihMajor ihContinuation =>
      simp only [checkClocks, List.mem_cons, List.mem_append] at h
      have hMajorEnd := finish_strict major start
      have hContinuationEnd := finish_strict continuation (finish major start)
      simp only [finish]
      rcases h with hEntry | hMajor | hRoot | hContinuation
      · subst clock
        exact ⟨Nat.le_refl _, Nat.lt_trans hMajorEnd
          (Nat.lt_trans hContinuationEnd (Nat.lt_succ_self _))⟩
      · have hb := ihMajor start hMajor
        exact ⟨hb.1, Nat.lt_trans hb.2
          (Nat.lt_trans hContinuationEnd (Nat.lt_succ_self _))⟩
      · subst clock
        exact ⟨Nat.le_of_lt hMajorEnd,
          Nat.lt_trans hContinuationEnd (Nat.lt_succ_self _)⟩
      · have hb := ihContinuation (finish major start) hContinuation
        exact ⟨Nat.le_trans (Nat.le_of_lt hMajorEnd) hb.1,
          Nat.lt_trans hb.2 (Nat.lt_succ_self _)⟩

/-- The name reserved by a call's return was not consumed inside that call. -/
theorem return_unused (t : Trace) (start : Nat) :
    finish t start ∉ allocations t start := by
  intro h
  have hb := allocation_bounds t start (finish t start) h
  omega

/-- Its reservation is later than every modeled check in the subtree. -/
theorem return_after_checks (t : Trace) (start clock : Nat)
    (h : clock ∈ checkClocks t start) : clock < finish t start :=
  (checkClock_bounds t start clock h).2

theorem before_node_allocation (major : Trace) (start name : Nat)
    (h : name ∈ allocations major start) : name < finish major start :=
  (allocation_bounds major start name h).2

theorem after_node_allocation (major continuation : Trace) (start name : Nat)
    (h : name ∈ allocations continuation (finish major start)) :
    finish major start < name :=
  (allocation_bounds continuation (finish major start) name h).1

/-- Earlier and continuation allocations cannot collide. -/
theorem branch_order (major continuation : Trace) (start earlier later : Nat)
    (hEarlier : earlier ∈ allocations major start)
    (hLater : later ∈ allocations continuation (finish major start)) :
    earlier < later := by
  have h₁ := before_node_allocation major start earlier hEarlier
  have h₂ := after_node_allocation major continuation start later hLater
  omega

/-- An old context can use any finite collection of names at or below the
entry clock.  A newly consumed inference name is distinct from each one. -/
theorem allocation_fresh_from_old (t : Trace) (start name old : Nat)
    (hName : name ∈ allocations t start) (hOld : old ≤ start) : name ≠ old := by
  have hb := allocation_bounds t start name hName
  omega

theorem return_fresh_from_old (t : Trace) (start old : Nat)
    (hOld : old ≤ start) : finish t start ≠ old := by
  have hf := finish_strict t start
  omega

/-- The reserved return name avoids both an old context and every consumed
name in the subtree.  This is the fact a parent call needs after its major. -/
theorem return_fresh_from_context_and_subtree
    (t : Trace) (start : Nat) (old : List Nat)
    (hOld : ∀ name ∈ old, name ≤ start) :
    finish t start ∉ old ++ allocations t start := by
  intro h
  simp only [List.mem_append] at h
  rcases h with hContext | hSubtree
  · have ho := hOld (finish t start) hContext
    have hf := finish_strict t start
    omega
  · exact return_unused t start hSubtree

/-- Conversion back to the decreasing integer levels used by the checker. -/
def level (clock : Nat) : Int := -(clock : Int)

theorem return_level_below_entry (t : Trace) (start : Nat) :
    level (finish t start) < level start := by
  have h := finish_strict t start
  simp only [level]
  omega

theorem return_level_below_allocations (t : Trace) (start name : Nat)
    (h : name ∈ allocations t start) :
    level (finish t start) < level name := by
  have hb := allocation_bounds t start name h
  simp only [level]
  omega

/-- Direct floor form: if all old free levels are at least the entry floor,
the freshly returned lower level is absent from that old context. -/
theorem return_level_fresh_from_floor_bound
    (t : Trace) (start : Nat) (oldLevels : List Int)
    (hOld : ∀ x ∈ oldLevels, level start ≤ x) :
    level (finish t start) ∉ oldLevels := by
  intro h
  have ho := hOld (level (finish t start)) h
  have hf := return_level_below_entry t start
  omega

#print axioms finish_eq
#print axioms finish_strict
#print axioms allocation_bounds
#print axioms checkClock_bounds
#print axioms return_unused
#print axioms branch_order
#print axioms return_fresh_from_context_and_subtree
#print axioms return_level_fresh_from_floor_bound

end FreshReturn
