/-!
Auxiliary native Lean specification.  This is NOT yet a proof in the
object theory ConciseIPRA.PRAAx.  No external mathlib imports required.
-/
namespace IPRAFramework

def testUpTo (p : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => testUpTo p n || p n

def firstUpTo (p : Nat → Bool) (bound : Nat) : Nat :=
  (List.range bound).foldl (fun answer i =>
    if answer == bound && p i then i else answer) bound

def iterate (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => iterate f n (f x)

theorem testUpTo_zero (p : Nat → Bool) : testUpTo p 0 = false := rfl

theorem testUpTo_succ (p : Nat → Bool) (n : Nat) :
    testUpTo p (n + 1) = (testUpTo p n || p n) := rfl

theorem iterate_zero (f : Nat → Nat) (x : Nat) :
    iterate f 0 x = x := rfl

theorem iterate_succ (f : Nat → Nat) (n x : Nat) :
    iterate f (n + 1) x = iterate f n (f x) := rfl

-- Next milestones are explicitly stated in ROADMAP.md: prove an invariant
-- for firstUpTo, define PR codes, and transport proofs into PRAAx.
end IPRAFramework
