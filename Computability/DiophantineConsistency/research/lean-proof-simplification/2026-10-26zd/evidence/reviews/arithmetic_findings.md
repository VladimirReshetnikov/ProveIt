# New arithmetic/encoding opportunities at 89226e3921

All source links below use the immutable commit
`89226e3921bce3e8949fadd12d3efb6914c7630c`.

## 1. Exact order certificates indexed by prime factors

Target `CurrentControllerData2011.lean`, especially `two_order_2011` (71–83),
with secondary client `two_order_47` (62–68). Replace the handwritten nested
prime-divisor analysis of 402=2*3*67 by the checked finite set
`(402:Nat).primeFactors = {2,3,67}`. The existing mathlib theorem
`orderOf_eq_of_pow_and_pow_div_prime` remains the mathematical criterion;
`Nat.mem_primeFactors` connects its universal prime-divisor premise with the
finite certificate. This is different from prior tile table/chunk dispatch:
the table here represents the factorization of the *candidate order*, and
its membership theorem is the bridge that makes the test complete.

The artifact `PrimeFactorOrder.lean` contains a generic bridge and exact 2011
and 47 examples. It is NOT compiler-validated here. The concrete production
candidate in `prime-factor-order.patch` discharges each complete finite
prime-factor certificate with `by decide`. It reduces the complete module
from 184 to 178 physical lines, including its six-line bridge and one added
import. Thus six net lines are removed at the pinned source; elaboration and
checking cost of the closed `decide` certificates remain to be measured.
Do not use native_decide or omit the n>0 condition.

Verified mathlib v4.32 API sources:
https://github.com/leanprover-community/mathlib4/blob/v4.32.0/Mathlib/Data/Nat/PrimeFin.lean
`Nat.mem_primeFactors` at line39:
`p ∈ n.primeFactors ↔ p.Prime ∧ p ∣ n ∧ n ≠ 0`.
https://github.com/leanprover-community/mathlib4/blob/v4.32.0/Mathlib/GroupTheory/OrderOfElement.lean
`orderOf_eq_of_pow_and_pow_div_prime` at line342 takes `(hn : 0 < n)`.

## 2. Numeric control overwrites preserve pointwise cell invariants

Target `CurrentWordConstruction2011.word`, `word_boolean`, and `word_support`;
secondary target `CurrentWordLowMask2011.assembled_capacity`.
The assembled cell is exactly the local digit function with marker1004 and
dummy977 overwritten. A proof-side `Function.update` view keeps the public
executable definition untouched. Mathlib's `Function.forall_update_iff`
provides the required general invariant law; no new induction or field
partition is necessary. Boolean, support and capacity proofs instantiate
that law. Unlike a copied-field direction descriptor, this handles mutable
numeric control values while leaving the tile's data fields unchanged.

Important correction: public `word_support` has no Boolean-control premises.
One must instantiate the invariant with support alone to preserve that
statement. The stronger conjunctive invariant can simplify other clients,
but cannot replace the support theorem by a version assuming hd/hm.

`ControlSlotCore.lean` compiles on Lean 4.32.0 with four theorem axiom
reports containing only propext; it proves overwrite preservation for
support, Boolean range and capacities and checks both literal slots, an
unaffected slot, and repeated-slot priority. `ControlSlotInvariant.lean`
supplies the production proof mechanism and exact binding, marked uncompiled. Its helper cost is not yet paid back by a measured
production patch: this is a maintainability proposal with explicit costs,
not a guaranteed immediate line reduction. Additional dummy/marker slots
would use the same overwrite law; old prior proposals on semantic locality
of Expr under valuation agreement are related but not this digit invariant.

Verified mathlib v4.32 API source:
https://github.com/leanprover-community/mathlib4/blob/v4.32.0/Mathlib/Logic/Function/Basic.lean
`Function.update_apply` line662; `Function.forall_update_iff` line680.

## Rejected as overlap

* Origin subtraction/no-borrow reduction: prior packet a digit notes §6 and
  g `WordOriginRefactor.lean` already supply `word_sub_origin`; forward mask
  encoding is largely the old API plus mask_capacity. Exact fixed-witness
  iff might still be useful, but cannot be sold as a new no-borrow idea.
* Cyclic carry uniqueness and reset uniqueness: j and k already cover the
  exceptional zero/all-maximum cases, exact least/greatest formulas and
  finite maximum principles.
* Generic reflected parity projection: packet o explicitly rejects it as
  overlapping old carry decomposition/modular projection proposals.
