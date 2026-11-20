import Std

/-!
# Constructive logical shell for a possible arithmetic proof of Robin's theorem

This file DOES NOT prove Robin's theorem.  In particular it does not implement
the analytic zero checker, nor prove either analytic certificate transformation.
The missing transformations are explicit theorem parameters, never axioms.

Each Boolean checker in an iPRA instantiation must be one *fixed* primitive
recursive function.  A Lean value of type `Nat -> Bool` is not by itself a proof
of primitive recursiveness, and this file makes no universal PR-evaluator claim.

The file uses only the Lean standard library, has no `sorry`, custom axiom,
`Classical` declaration, `native_decide`, or choice operation.  The final
`#print axioms` commands make its actual logical dependencies visible.
-/

namespace RobinCertificateLogic

structure Checkers where
  positive : Nat -> Nat -> Bool
  negative : Nat -> Nat -> Bool
  badZero : Nat -> Bool

def PositiveAt (c : Checkers) (n : Nat) : Prop :=
  Exists (fun k => c.positive n k = true)

def RobinStrict (c : Checkers) : Prop :=
  forall n, 5040 < n -> PositiveAt c n

def RobinDoubleNeg (c : Checkers) : Prop :=
  forall n, 5040 < n -> Not (Not (PositiveAt c n))

def RobinWeak (c : Checkers) : Prop :=
  forall n, 5040 < n -> forall k, Not (c.negative n k = true)

def RHNegative (c : Checkers) : Prop :=
  forall z, Not (c.badZero z = true)

/-- Rational interval soundness implies this finite incompatibility property. -/
def SignDisjoint (c : Checkers) : Prop :=
  forall n k j, c.positive n k = true -> c.negative n j = true -> False

theorem strict_implies_doubleNeg (c : Checkers) :
    RobinStrict c -> RobinDoubleNeg c := by
  intro h n hn hnot
  exact hnot (h n hn)

theorem doubleNeg_implies_weak (c : Checkers) (hd : SignDisjoint c) :
    RobinDoubleNeg c -> RobinWeak c := by
  intro h n hn j hj
  apply h n hn
  intro hp
  cases hp with
  | intro k hk => exact hd n k j hk hj

theorem strict_implies_weak (c : Checkers) (hd : SignDisjoint c) :
    RobinStrict c -> RobinWeak c := by
  intro h
  exact doubleNeg_implies_weak c hd (strict_implies_doubleNeg c h)

/-- A no-bad-certificate statement is intuitionistically stable. -/
theorem rhNegative_stable (c : Checkers) :
    Not (Not (RHNegative c)) -> RHNegative c := by
  intro h z hz
  apply h
  intro hrh
  exact hrh z hz

theorem robinWeak_stable (c : Checkers) :
    Not (Not (RobinWeak c)) -> RobinWeak c := by
  intro h n hn k hk
  apply h
  intro hw
  exact hw n hn k hk

/-- Contraposition with stable conclusion is valid without excluded middle. -/
theorem converse_of_contrapositive (c : Checkers)
    (h : Not (RHNegative c) -> Not (RobinStrict c)) :
    RobinStrict c -> RHNegative c := by
  intro hs
  apply rhNegative_stable c
  intro hnrh
  exact h hnrh hs

/-- The translated converse suffices for the original converse. -/
theorem converse_of_translated_converse (c : Checkers)
    (h : RobinDoubleNeg c -> RHNegative c) :
    RobinStrict c -> RHNegative c := by
  intro hs
  exact h (strict_implies_doubleNeg c hs)

/-!
The following theorem is a deliberately conditional assembly lemma.

`forwardCover` is a positive, finite-witness alternative: for each n > 5040,
an explicit bad-zero certificate or an explicit strictly positive Robin margin.
`reverseWitness` sends each valid bad-zero certificate to a strictly negative
Robin margin at an explicitly selected integer > 5040.

Producing fixed primitive recursive functions for these four selectors and
proving the two displayed hypotheses in iPRA is the substantive uncompleted
analytic work.  This file establishes only that those data would suffice.
-/
theorem criterion_of_certificate_transforms
    (c : Checkers) (hd : SignDisjoint c)
    (forwardBad forwardPrec reverseN reversePrec : Nat -> Nat)
    (forwardCover : forall n, 5040 < n ->
      Or (c.badZero (forwardBad n) = true)
         (c.positive n (forwardPrec n) = true))
    (reverseWitness : forall z, c.badZero z = true ->
      And (5040 < reverseN z)
          (c.negative (reverseN z) (reversePrec z) = true)) :
    Iff (RHNegative c) (RobinStrict c) := by
  constructor
  · intro hrh n hn
    cases forwardCover n hn with
    | inl hz => exact False.elim (hrh (forwardBad n) hz)
    | inr hp => exact Exists.intro (forwardPrec n) hp
  · intro hs z hz
    have hw : RobinWeak c := strict_implies_weak c hd hs
    have hr := reverseWitness z hz
    exact hw (reverseN z) hr.left (reversePrec z) hr.right

/-!
An interval constantly equal to [0,0] has no strictly negative certificate but
also has no strictly positive certificate.  This is a concrete counterexample
to the *generic* replacement of strict positivity by absence of negativity.
It is not a statement that any actual Robin gap vanishes.
-/
def zeroGapCheckers : Checkers where
  positive := fun _ _ => false
  negative := fun _ _ => false
  badZero := fun _ => false

theorem zeroGap_is_weak : RobinWeak zeroGapCheckers := by
  intro _ _ _ h
  exact Bool.noConfusion h

theorem zeroGap_is_not_strict : Not (RobinStrict zeroGapCheckers) := by
  intro hs
  have hp := hs 5041 (by decide)
  cases hp with
  | intro _ hk => exact Bool.noConfusion hk

theorem zeroGap_is_not_doubleNeg : Not (RobinDoubleNeg zeroGapCheckers) := by
  intro hs
  apply hs 5041 (by decide)
  intro hp
  cases hp with
  | intro _ hk => exact Bool.noConfusion hk

/-!
Primitive-recursive bounded search.  For any *fixed* PR predicate p, these are
PR functions and the displayed loop invariants are quantifier-free (with p
instantiated).  They show precisely why a supplied bound is adequate, without
equating an unbounded successful search with primitive recursion.
-/
def anyUpTo (p : Nat -> Bool) : Nat -> Bool
  | 0 => p 0
  | n + 1 => anyUpTo p n || p (n + 1)

def pickUpTo (p : Nat -> Bool) : Nat -> Nat
  | 0 => 0
  | n + 1 => match p (n + 1) with
      | true => n + 1
      | false => pickUpTo p n

theorem pickUpTo_le (p : Nat -> Bool) (b : Nat) : pickUpTo p b <= b := by
  induction b with
  | zero => exact Nat.le_refl 0
  | succ b ih =>
    cases h : p (b + 1) with
    | false =>
      rw [pickUpTo, h]
      exact Nat.le_trans ih (Nat.le_succ b)
    | true =>
      rw [pickUpTo, h]
      exact Nat.le_refl (b + 1)

theorem pickUpTo_correct (p : Nat -> Bool) (b : Nat) :
    anyUpTo p b = true -> p (pickUpTo p b) = true := by
  induction b with
  | zero => exact fun h => h
  | succ b ih =>
    intro hb
    cases h : p (b + 1) with
    | false =>
      rw [anyUpTo, h, Bool.or_false] at hb
      rw [pickUpTo, h]
      exact ih hb
    | true =>
      rw [pickUpTo, h]
      exact h

#print axioms strict_implies_doubleNeg
#print axioms doubleNeg_implies_weak
#print axioms rhNegative_stable
#print axioms converse_of_contrapositive
#print axioms criterion_of_certificate_transforms
#print axioms zeroGap_is_not_strict
#print axioms pickUpTo_le
#print axioms pickUpTo_correct

end RobinCertificateLogic
