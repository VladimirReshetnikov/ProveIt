# Proof and scope audit

## Mathematical result

For a finite nonempty skeleton Q with fibres omega^rho_q (rho_q > 0), the
height of its finitary-downset poset is exactly the maximum retirement-path
cost on the Hoare-ordered inclusion-maximal antichains. The height is attained
by an explicit chain. Finite monomial-block expansion covers arbitrary
nonzero limit-ordinal fibres, with no countability restriction.

## Logical dependency chain

1. Unique finite-generator profiles and the shared-coordinate order criterion.
2. The minimal completion A -> A union min(Inc(A)) is the least maximal
   antichain Hoare-above A; a genuinely retired old vertex cannot reappear
   as a filler in the target completion.
3. Shift original coordinates by LEFT ordinal addition 1+x and give filler
   coordinates value 0. This yields a strict height-comparison map from all
   profiles, including the empty profile, to maximal-support profiles.
4. Descending sequences with a finite monotone index are covered by finitely
   many prefix-closed descending trees indexed by chains. The rank of such
   a finite union is the maximum of the ranks.
5. In a retirement box, group capacities are maxima of pure infinite powers.
   Before the last largest group retires, count retired large GROUPS in the
   leading coefficient and use the natural sum of active values plus retired
   SMALL coordinate capacities for the residual. The residual is below the
   leading pure power, and the whole map is strictly increasing.
6. No vertex returns after leaving a frontier chain. This gives disjoint
   retirement groups and a strict map from one path's profiles into a box.
   Varying one pivot coordinate in each group constructs the matching chain.
7. Combine steps 3, 4, and 6. Refining a path cannot decrease its ordinal cost.
8. Expand a nonzero limit fibre into its finite positive-exponent CNF blocks.

## Delicate points checked in the written proof

- Height is the well-founded rank / descending-tree invariant, not maximal
  order type. No maximal-linearization theorem is invoked.
- A cofinal suborder need not preserve height. Step 3 supplies a STRICT map,
  rather than assuming cofinality suffices.
- The tree-union argument covers entire descending sequences. An arbitrary
  finite union of induced subposets does not have height equal to their max.
- Shared coordinates persist across frontier transitions. They are not reset.
- Finite natural sums below a pure power remain below it; infinite sums need
  not. Both the skeleton and coordinate groups are finite.
- The group count in the prefix bound counts groups with maximum capacity
  Lambda, not all individual coordinates of capacity Lambda.
- Main path costs use ordinary ordinal addition; the auxiliary residual uses
  natural addition. Their roles are not interchangeable.
- The last group is not retired. It supplies the terminal term, without an
  additional top point or successor.
- Pure-fibre exponents are positive. Finite fibres and successor tails are
  not covered by the extension theorem.
- The empty skeleton is a separate implementation case: K(empty) has height 1.

## Attribution and novelty boundary

The uniform formula, and the example of an isolated omega^2 coordinate next
to a chain of two omega fibres, occur in the inspected ProveIt report.
They are explicitly credited. Basic rank facts, natural-sum arithmetic, and
product-of-ordinal rank identities are standard background, reproved when
used. No priority is claimed for elementary supporting lemmas.

The contribution advanced here is the general nonuniform retirement formula,
its proof architecture, and the resulting finite computation for all nonzero
limit-ordinal chain fibres. The paired stratum-isomorphism counterexample and
coefficient-pattern consequences clarify its scope. Independent priority
certification has not been performed.

## Verification

`code/verify.py` passed 3,210,888 assertions. It checks 5,231 nonempty naturally
labelled posets through six vertices and 128,793 weighted instances. All
exponent assignments in {1,2,3}^n are tested through n=5. Eight deterministic
assignments are used at n=6. Independent all-chain / word-erasure comparisons
cover 90,201 weighted instances. Limit-block expansion has separate chain and
ordinal-product oracles (258 instances each).

No test computes infinite descending-tree ranks, proves a theorem for all
ordinals, or establishes novelty. No Lean or other proof-assistant check has
been run. The code was written for this package rather than copied from the
repository's separate maximal-order-type implementation.

## Not claimed

No formula for arbitrary non-chain WPO fibres, width, maximal order type,
iterated finitary powersets, infinite skeletons, or finite/successor ordinal
fibres. No large-cardinal consistency or inconsistency conclusion. No
polynomial-time bound in the original skeleton size. No repository write.
