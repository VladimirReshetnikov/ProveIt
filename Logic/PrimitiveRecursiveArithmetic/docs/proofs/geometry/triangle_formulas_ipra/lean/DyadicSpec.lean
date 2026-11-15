import Mathlib.Data.Rat.Defs

/-!
# A bounded rational square-root algorithm and its exact target

STATUS: executable-definition / theorem-statement outline, not compiled in
this environment. `RootCorrectness` below is a proposition naming a missing
formal proof, not a theorem claiming that proof has been completed.
-/

namespace TriangleIPRA.Dyadic

/-- Scan all `j ≤ bound`, retaining the largest one with `q*j^2 ≤ p*scale^2`.
The scan is total even when `q = 0`; correctness is stated only for `q > 0`.
This is a primitive recursion in the explicit natural-number bound. -/
def rootScan (p q scale : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      let previous := rootScan p q scale n
      if q * (n + 1) ^ 2 ≤ p * scale ^ 2 then n + 1 else previous

/-- The explicit upper bound works because `sqrt(p/q) ≤ p+1` for `q ≥ 1`. -/
def rootFloor (p q k : ℕ) : ℕ :=
  if q = 0 then 0 else rootScan p q (2 ^ k) ((p + 1) * 2 ^ k)

def rootLower (p q k : ℕ) : ℚ :=
  (rootFloor p q k : ℚ) / (2 : ℚ) ^ k

/-- The interval `[r/2^k,(r+1)/2^k]` brackets the nonnegative square root. -/
def RootBracket (p q k r : ℕ) : Prop :=
  q * r ^ 2 ≤ p * (2 ^ k) ^ 2 ∧
    p * (2 ^ k) ^ 2 < q * (r + 1) ^ 2

instance (p q k r : ℕ) : Decidable (RootBracket p q k r) :=
  inferInstanceAs (Decidable
    (q * r ^ 2 ≤ p * (2 ^ k) ^ 2 ∧ p * (2 ^ k) ^ 2 < q * (r + 1) ^ 2))

/-- A total natural-number check: zero means success; invalid denominator
input is assigned a fixed successful value, without representing a rational. -/
def rootCheck (p q k : ℕ) : ℕ :=
  if q = 0 then 0 else
    if RootBracket p q k (rootFloor p q k) then 0 else 1

/-- MISSING FORMALIZATION OBLIGATION: establish this by bounded scan induction.
The paper gives the complete human proof. -/
def RootCorrectness : Prop :=
  ∀ p q k : ℕ, 0 < q → RootBracket p q k (rootFloor p q k)

/-- Equivalently, this Boolean/characteristic target is quantifier-free before
universal closure and can be represented by one equation in iPRA. -/
def RootCheckCorrectness : Prop := ∀ p q k : ℕ, rootCheck p q k = 0

end TriangleIPRA.Dyadic
