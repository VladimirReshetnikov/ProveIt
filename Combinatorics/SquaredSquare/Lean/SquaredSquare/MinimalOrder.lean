import SquaredSquare.Duijvestijn
import SquaredSquare.Scaling
import SquaredSquare.Minimality

/-!
# The minimal order of a perfect squared square

This module packages the minimality statement itself.  `perfectOrders` is
the set of piece counts realized by perfect squared squares (of any side).
It is proved here that

* `21 ∈ perfectOrders` (Duijvestijn's dissection),
* every member is at least `7` (the elementary lower bound), and
* the full minimality statement `IsLeast perfectOrders 21` is *equivalent*
  to the single proposition `DuijvestijnSearchClaim` — no perfect squared
  square has fewer than 21 pieces — which is exactly the result of
  A. J. W. Duijvestijn's 1978 exhaustive computer search.

`DuijvestijnSearchClaim` is stated, reduced to, and bracketed
(`7 ≤ n` for every achievable order `n`), but **not proved**: no axiom is
introduced for it, and `IsLeast perfectOrders 21` is therefore not asserted
as a theorem here.  See the project README for the status and sizing of a
full formalization.
-/

namespace LeanProofs

namespace SquaredSquare

/-- The set of piece counts realized by perfect squared squares. -/
def perfectOrders : Set ℕ :=
  {n | ∃ (S : ℝ) (l : List Sq), IsPerfectSquaredSquare S l ∧ l.length = n}

/-- The result of Duijvestijn's exhaustive search, as a proposition: every
perfect squared square has at least 21 pieces.  Not proved in this
repository. -/
def DuijvestijnSearchClaim : Prop :=
  ∀ (S : ℝ) (l : List Sq), IsPerfectSquaredSquare S l → 21 ≤ l.length

/-- Order 21 is achieved (Duijvestijn's dissection). -/
theorem mem_perfectOrders_21 : 21 ∈ perfectOrders :=
  ⟨112, duijvestijnTiles, duijvestijn_perfect, duijvestijnTiles_length⟩

/-- Every achievable order is at least 7 (the elementary lower bound). -/
theorem seven_le_of_mem_perfectOrders : ∀ n ∈ perfectOrders, 7 ≤ n := by
  rintro n ⟨S, l, hp, rfl⟩
  exact seven_le_length hp

/-- **The minimality statement, reduced.**  "The minimal number of pieces
of a perfect squared square is 21" holds if and only if Duijvestijn's
search claim does.  The forward direction is immediate; the backward
direction combines the claim with Duijvestijn's dissection. -/
theorem isLeast_perfectOrders_iff :
    IsLeast perfectOrders 21 ↔ DuijvestijnSearchClaim := by
  constructor
  · rintro ⟨-, hlb⟩ S l hp
    exact hlb ⟨S, l, hp, rfl⟩
  · intro h
    refine ⟨mem_perfectOrders_21, ?_⟩
    rintro n ⟨S, l, hp, rfl⟩
    exact h S l hp

end SquaredSquare

end LeanProofs
