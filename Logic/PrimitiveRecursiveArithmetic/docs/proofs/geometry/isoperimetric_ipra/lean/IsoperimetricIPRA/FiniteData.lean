import Mathlib

/-!
# Finite rational data for the planar isoperimetric argument

STATUS: UNCOMPILED BLUEPRINT. The definitions below specify executable finite
data and the intended proposition. This file does not prove the isoperimetric
inequality. No real-number type or real-number choice operation is used in
these definitions. A proof in Lean's ambient logic would still need the
separate internal-iPRA construction described in `InternalGoal.lean`.

Target environment: ProveIt commit
329161f8da0b319d51ba9f6246c4b19d243f7193, Lean 4.32.0.
-/

namespace IsoperimetricIPRA

structure Point where
  x : ℚ
  y : ℚ
  deriving DecidableEq, Repr

def cross (p q : Point) : ℚ := p.x * q.y - p.y * q.x

def edgeNormSq (p q : Point) : ℚ :=
  (q.x - p.x) ^ 2 + (q.y - p.y) ^ 2

/-- Consecutive edges followed by the closing edge. -/
def edgesFrom (first current : Point) : List Point → List (Point × Point)
  | [] => [(current, first)]
  | next :: rest => (current, next) :: edgesFrom first next rest

def edges : List Point → List (Point × Point)
  | [] => []
  | first :: rest => edgesFrom first first rest

/-- Signed shoelace area. Self-intersections are permitted. -/
def area (p : List Point) : ℚ :=
  ((edges p).map fun e => cross e.1 e.2).sum / 2

def dyadic (k : ℕ) : ℚ := 1 / (2 : ℚ) ^ k

/-- Largest accepted natural at most the supplied bound; zero is the
fallback. The square-root test below accepts zero whenever its input is
nonnegative. Every recursion is bounded by an explicit natural. -/
def boundedMax (test : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if test (n + 1) then n + 1 else boundedMax test n

/-- Downward dyadic square-root approximation, without a real square root.

For nonnegative rational `x`, the obligations are
`0 ≤ sqrtDown x t`, `(sqrtDown x t)^2 ≤ x`, and
`x < (sqrtDown x t + dyadic t)^2`.
The bound is deliberately coarse: `sqrt x < |x.num| + 1`.
On negative input this total definition returns zero.
-/
def sqrtDown (x : ℚ) (t : ℕ) : ℚ :=
  let scale : ℕ := 2 ^ t
  let bound : ℕ := scale * (x.num.natAbs + 1)
  let j := boundedMax
    (fun n => decide ((n : ℚ) ^ 2 ≤ (scale : ℚ) ^ 2 * x)) bound
  (j : ℚ) / (scale : ℚ)

/-- After `n` steps this approximates `cos(pi / 2^(n+1))` from below.
That interpretation is an obligation, not a theorem asserted by this file. -/
def cosineApprox (t : ℕ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => sqrtDown ((1 + cosineApprox t n) / 2) t

/-- The explicit rational lower approximation prescribed by the report. -/
def piLower (k : ℕ) : ℚ :=
  let r := k + 4
  let t := 4 * k + 16
  let h := dyadic t
  let cHat := cosineApprox t (r - 1)
  let cBar := min 1 (cHat + 2 * h)
  (2 : ℚ) ^ r * sqrtDown (1 - cBar ^ 2) t

/-- Finite input validity. The upper-length list has exactly one entry
per polygon edge, and each entry bounds that edge's Euclidean length. -/
def validUpperLengths (p : List Point) (u : List ℚ) : Bool :=
  decide (p ≠ []) &&
  decide (u.length = p.length) &&
  (((edges p).zip u).all fun eu =>
    decide (0 ≤ eu.2 ∧ edgeNormSq eu.1.1 eu.1.2 ≤ eu.2 ^ 2))

def finiteInequality (p : List Point) (u : List ℚ) (k : ℕ) : Prop :=
  4 * piLower k * |area p| ≤ u.sum ^ 2 + dyadic k

/-- Invalid finite data are accepted vacuously. Thus the target can be one
equation for a total primitive-recursive Boolean checker. -/
def finiteCheck (p : List Point) (u : List ℚ) (k : ℕ) : Bool :=
  !validUpperLengths p u || decide (finiteInequality p u k)

/-- This is the desired finite theorem's TYPE, not a proof of it. -/
def FiniteTheorem : Prop :=
  ∀ (p : List Point) (u : List ℚ) (k : ℕ),
    validUpperLengths p u = true → finiteInequality p u k

/- Remaining finite-mathematical obligations:

1. Correctness and total PR coding of `boundedMax`, rational arithmetic,
   `sqrtDown`, lists, area, and all bounded Boolean predicates.
2. Lower bounds and an explicit convergence modulus for `piLower`.
3. Ordered nested-radical arithmetic and the finite dyadic-root DFT identity.
4. The DFT area/energy inequality and exact invariance of area under rational
   subdivision of polygon edges.
5. The explicitly bounded subdivision estimate in the accompanying report.
6. The final rational comparison `finiteCheck p u k = true`.

Those obligations must then be proved inside the embedded iPRA calculus.
Merely evaluating this checker on sample inputs is not a universal proof.
-/

end IsoperimetricIPRA
