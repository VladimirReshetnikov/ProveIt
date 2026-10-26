# Independent mathematical review of arithmetic candidates

Reviewed files: arithmetic_notes/PrimeFactorOrder.lean,
prime-factor-order.patch, ControlSlotInvariant.lean, ControlSlotCore.lean.
This review is source inspection and independent mathematics. It does not
constitute an integrated mathlib build.

## Prime-factor order certificate

The generic criterion is sound for every monoid. The existing theorem
orderOf_eq_of_pow_and_pow_div_prime requires n>0, x^n=1, and nontriviality
at n/p for every prime divisor p of n. The proposed bridge converts such a
prime divisor to membership in n.primeFactors using the exact library
identity p∈n.primeFactors iff p.Prime ∧ p∣n ∧ n≠0. The n≠0 premise follows
from retained n>0. No primality of the modulus or cancellative ambient
monoid is silently added.

The concrete sets are primeFactors(23)={23} and primeFactors(402)={2,3,67}.
The latter powers have residues 2010,205,64 modulo2011, all unequal to1;
2^(23/23)=2 modulo47, also unequal to1. The source's exact order targets
are therefore justified. The shorter production patch closes the finite
bounded universal proposition with `decide`; no native_decide or additional
axiom is used. Its exact elaboration and runtime still require integrated
Lean replay before adoption, because this reviewer has not checked that
mathlib-dependent candidate.

Independent inspection of pinned mathlib v4.32.0 confirmed:
- Data/Nat/PrimeFin.lean:39: mem_primeFactors, conjunction order as above.
- GroupTheory/OrderOfElement.lean:342: orderOf_eq_of_pow_and_pow_div_prime,
  positive candidate order and exactly the prime-divisor exclusion premise.

## Controlled cell overwrites

The nesting update(update(localDigit,1004,marker),977,dummy) agrees with the
literal branch priority: dummy at977, else marker at1004, else localDigit.
The proposal changes only a proof-side view of the word. Mathlib's exact
forall_update_iff f P statement, inspected in Function/Basic.lean:680, is
(∀x,P x (update f a b x)) iff P a b ∧ ∀x,x≠a→P x (f x).
The sufficient-form helper supplies the old invariant at every unaffected
position and checks the new value at the update coordinate. No distinctness
premise is needed; repeated writes obey the outer update's priority.

Important public-contract constraint: original word_support has no Boolean
assumptions for either control. Its replacement must instantiate support
alone, not project from a conjunction that assumes dummy≤1 and marker≤1.
The existing artifact explicitly records this restriction. The abstract
controlled_capacity theorem also requires separate bounds for both values;
those must be derived at the actual support slots in a production client.
Neither control may be equated with zero or with each other. The shifted
Start interpretation of a marker is separate and is not implied.

An independent fresh core replay after the initial simp correction completed
with exit code0; control_slot_independent_replay.log lists only [propext] for overwrite_preserves, controlled_support,
controlled_boolean, and controlled_capacity. This supports the abstract
mechanism only; it does not validate Function.update binding, concrete
lowSupport reduction, or the imported word module.

Recommendation: accept both as sound, explicitly bounded proposals. Count
six net lines only for the prime-factor patch (including its helper/import)
after separate patch metrics verification. For the control view, keep the
helper cost visible and avoid claiming a source reduction until actual
word/support/capacity client edits are measured.
