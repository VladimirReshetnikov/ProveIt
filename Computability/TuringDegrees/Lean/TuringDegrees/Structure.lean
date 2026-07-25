import TuringDegrees.Halting

/-!
# Structural notions from the Turing-degree literature

This file gives precise formulations of the order-theoretic and approximation
notions used on the Wikipedia page.  The celebrated existence theorems about
minimal degrees, exact pairs, jump inversion, and priority constructions are
not postulated.  Instead, we prove every consequence which follows purely from
the stated witness.  This keeps the boundary between elementary order theory
and deep computability theory explicit.

The page's displayed exact-pair formula uses strict common lower bounds.  The
standard useful formulation below uses non-strict common lower bounds together
with explicit strict upper-bound clauses; this is the formulation from which
the advertised no-least-upper-bound result follows.
-/

noncomputable section

namespace TuringDegrees

open scoped SetTuring

section OrderTheory

variable {D : Type*} [PartialOrder D]

/-- Two degrees (or elements of any partial order) are incomparable. -/
def Incomparable (a b : D) : Prop :=
  ¬a ≤ b ∧ ¬b ≤ a

/-- The order relation is total.  This proposition is kept separate from a
`LinearOrder` instance because Turing degrees have no decidable comparison. -/
def IsLinearBy (D : Type*) [LE D] : Prop :=
  ∀ a b : D, a ≤ b ∨ b ≤ a

/-- The open interval between every strictly ordered pair is inhabited. -/
def IsDenseBy (D : Type*) [LT D] : Prop :=
  ∀ ⦃a b : D⦄, a < b → ∃ c, a < c ∧ c < b

theorem incomparable_not_linear {a b : D} (h : Incomparable a b) :
    ¬IsLinearBy D := by
  intro linear
  rcases linear a b with hab | hba
  · exact h.1 hab
  · exact h.2 hba

section Bottom

variable [OrderBot D]

/-- A minimal nonzero degree: every strict predecessor is zero. -/
def IsMinimalDegree (a : D) : Prop :=
  ⊥ < a ∧ ∀ ⦃b : D⦄, b < a → b = ⊥

theorem minimalDegree_ne_bot {a : D} (h : IsMinimalDegree a) : a ≠ ⊥ :=
  ne_of_gt h.1

/-- A minimal degree witnesses that the degree ordering is not dense. -/
theorem minimalDegree_not_dense {a : D} (h : IsMinimalDegree a) :
    ¬IsDenseBy D := by
  intro dense
  obtain ⟨b, hbotb, hba⟩ := dense h.1
  have : b = ⊥ := h.2 hba
  subst b
  exact (lt_irrefl (⊥ : D)) hbotb

end Bottom

/-- `m` is a greatest lower bound of `a` and `b`. -/
def IsGreatestLowerBound (a b m : D) : Prop :=
  m ≤ a ∧ m ≤ b ∧ ∀ ⦃d : D⦄, d ≤ a → d ≤ b → d ≤ m

def HasGreatestLowerBound (a b : D) : Prop :=
  ∃ m, IsGreatestLowerBound a b m

/-- The order has binary greatest lower bounds. -/
def HasAllBinaryInfima (D : Type*) [PartialOrder D] : Prop :=
  ∀ a b : D, HasGreatestLowerBound a b

theorem no_glb_not_all_binary_infima {a b : D}
    (h : ¬HasGreatestLowerBound a b) : ¬HasAllBinaryInfima D := by
  intro all
  exact h (all a b)

/-- Greatest lower bound relative to a distinguished subcollection, needed to
distinguish "GLB in the c.e. degrees" from a GLB in all Turing degrees. -/
def IsGreatestLowerBoundWithin (P : D → Prop) (a b m : D) : Prop :=
  P m ∧ m ≤ a ∧ m ≤ b ∧
    ∀ ⦃d : D⦄, P d → d ≤ a → d ≤ b → d ≤ m

/-- Least-upper-bound predicate for a sequence. -/
def IsSequenceLUB (sequence : ℕ → D) (upper : D) : Prop :=
  (∀ i, sequence i ≤ upper) ∧
    ∀ ⦃other : D⦄, (∀ i, sequence i ≤ other) → upper ≤ other

/-- An exact pair for a sequence: both components strictly bound the sequence,
and their common lower cone is exactly the downward closure of the sequence. -/
def IsExactPair (sequence : ℕ → D) (left right : D) : Prop :=
  (∀ i, sequence i < left ∧ sequence i < right) ∧
    ∀ e, (e ≤ left ∧ e ≤ right ↔ ∃ i, e ≤ sequence i)

/-- The exact-pair theorem implies the page's claim that an infinite strictly
increasing sequence has no least upper bound. -/
theorem exactPair_no_lub {sequence : ℕ → D} {left right : D}
    (increasing : StrictMono sequence)
    (exact : IsExactPair sequence left right) :
    ¬∃ upper, IsSequenceLUB sequence upper := by
  rintro ⟨upper, upperIsLUB⟩
  have upperLeLeft : upper ≤ left :=
    upperIsLUB.2 fun i => (exact.1 i).1.le
  have upperLeRight : upper ≤ right :=
    upperIsLUB.2 fun i => (exact.1 i).2.le
  obtain ⟨i, upperLeI⟩ := (exact.2 upper).mp ⟨upperLeLeft, upperLeRight⟩
  have nextLeUpper : sequence (i + 1) ≤ upper := upperIsLUB.1 (i + 1)
  have step : sequence i < sequence (i + 1) := increasing (Nat.lt_succ_self i)
  exact (not_lt_of_ge (nextLeUpper.trans upperLeI)) step

end OrderTheory

namespace SetTuringDegree

/-- A degree is c.e. iff it contains a computably enumerable set. -/
abbrev IsCEDegree := IsComputablyEnumerable

/-- `b` is low relative to `a` for a specified jump operation when it is a
strict extension of `a` with the same jump. -/
def IsLowRelative (jump : SetTuringDegree → SetTuringDegree)
    (a b : SetTuringDegree) : Prop :=
  a < b ∧ jump b = jump a

end SetTuringDegree

/-! ## Recursive approximations and the finite-change hierarchy -/

/-- A stage-indexed Boolean approximation converges pointwise to `A`.
Unlike the malformed one-variable formula on the page, both the element `x`
and stage `s` are explicit. -/
def EventuallyApproximates (g : ℕ → ℕ → Bool) (A : Set ℕ) : Prop :=
  ∀ x, ∃ firstStage, ∀ s, firstStage ≤ s → (g s x = true ↔ x ∈ A)

/-- The number of mind changes made for any input, in every finite initial
segment of stages, is bounded by `n`.  This formulation avoids assuming in
advance that the set of change stages is finite. -/
def HasChangeBound (n : ℕ) (g : ℕ → ℕ → Bool) : Prop :=
  ∀ x cutoff,
    ((Finset.range cutoff).filter fun s => g (s + 1) x != g s x).card ≤ n

/-- Corrected `n`-c.e. definition: a computable two-argument approximation,
initially false, converges pointwise and changes at most `n` times per input. -/
def IsNComputablyEnumerable (n : ℕ) (A : Set ℕ) : Prop :=
  ∃ g : ℕ → ℕ → Bool,
    Computable₂ g ∧
    (∀ x, g 0 x = false) ∧
    EventuallyApproximates g A ∧
    HasChangeBound n g

/-- A degree is `n`-c.e. when it *contains* an `n`-c.e. representative. -/
def SetTuringDegree.IsNComputablyEnumerable
    (n : ℕ) (degree : SetTuringDegree) : Prop :=
  ∃ A : Set ℕ, TuringDegrees.IsNComputablyEnumerable n A ∧
    SetTuringDegree.of A = degree

theorem HasChangeBound.mono {m n : ℕ} {g : ℕ → ℕ → Bool}
    (hmn : m ≤ n) (bound : HasChangeBound m g) : HasChangeBound n g := by
  intro x cutoff
  exact (bound x cutoff).trans hmn

theorem IsNComputablyEnumerable.mono {m n : ℕ} {A : Set ℕ}
    (hmn : m ≤ n) (hA : IsNComputablyEnumerable m A) :
    IsNComputablyEnumerable n A := by
  obtain ⟨g, computable, initial, converges, changes⟩ := hA
  exact ⟨g, computable, initial, converges, changes.mono hmn⟩

theorem SetTuringDegree.IsNComputablyEnumerable.mono
    {m n : ℕ} {degree : SetTuringDegree}
    (hmn : m ≤ n) (hdegree : degree.IsNComputablyEnumerable m) :
    degree.IsNComputablyEnumerable n := by
  obtain ⟨A, hA, rfl⟩ := hdegree
  exact ⟨A, hA.mono hmn, rfl⟩

end TuringDegrees
