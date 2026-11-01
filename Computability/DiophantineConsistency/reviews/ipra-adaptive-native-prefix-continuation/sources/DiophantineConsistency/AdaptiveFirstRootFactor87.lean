import Mathlib.Tactic.Ring

/-! A local semiring-level factorization for the adaptive first root.
The signed-pair identity is valid in every commutative semiring. It does not
bind a complete literal equation or claim any consistency equivalence. -/
set_option autoImplicit false
namespace DiophantineConsistency.AdaptiveFirstRootFactor87

abbrev SignedPair (R : Type*) := R × R

def pairAdd {R : Type*} [CommSemiring R] (p q : SignedPair R) : SignedPair R :=
  (p.1 + q.1, p.2 + q.2)

def pairNeg {R : Type*} (p : SignedPair R) : SignedPair R := (p.2, p.1)

def pairSub {R : Type*} [CommSemiring R] (p q : SignedPair R) : SignedPair R :=
  pairAdd p (pairNeg q)

def pairMul {R : Type*} [CommSemiring R] (p q : SignedPair R) : SignedPair R :=
  (p.1 * q.1 + p.2 * q.2, p.1 * q.2 + p.2 * q.1)

def pairOne {R : Type*} [CommSemiring R] : SignedPair R := (1, 0)

/-- The original and factored first-root expressions have exactly equal split
pairs for arbitrary signed inputs over any commutative semiring. -/
theorem signed_root_identity {R : Type*} [CommSemiring R]
    (q3 qm k bt g y : SignedPair R) :
    let m := pairMul q3 qm
    pairSub (pairAdd (pairMul m g) (pairMul y qm))
        (pairMul bt (pairMul (pairAdd pairOne (pairMul k qm)) q3)) =
      pairSub (pairAdd (pairMul m (pairSub g (pairMul k bt))) (pairMul y qm))
        (pairMul bt q3) := by
  apply Prod.ext <;> simp only [pairAdd, pairNeg, pairSub, pairMul, pairOne] <;> ring

/-- Any subsequent computation of the split pair has the same result. -/
theorem context_identity {R S : Type*} [CommSemiring R]
    (context : SignedPair R → S) (q3 qm k bt g y : SignedPair R) :
    let m := pairMul q3 qm
    context (pairSub (pairAdd (pairMul m g) (pairMul y qm))
        (pairMul bt (pairMul (pairAdd pairOne (pairMul k qm)) q3))) =
      context (pairSub (pairAdd (pairMul m (pairSub g (pairMul k bt))) (pairMul y qm))
        (pairMul bt q3)) := by
  exact congrArg context (signed_root_identity q3 qm k bt g y)

end DiophantineConsistency.AdaptiveFirstRootFactor87
