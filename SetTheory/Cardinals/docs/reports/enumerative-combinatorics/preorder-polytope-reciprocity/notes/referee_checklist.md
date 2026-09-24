# Referee-oriented proof checklist

## Imported results

1. Ehrhart–Macdonald reciprocity for a full-dimensional lattice polytope in
   its integer lattice. This is invoked only on positive parameter rays.
2. Postnikov, Theorem 11.3 in untrimmed form: the binomial factor belonging
   to the full-simplex neighborhood is choose(y0+a0,a0), whereas the other
   factors are choose(yi+ai-1,ai). Zero coefficients and repeated neighborhoods
   are allowed. The formula is also Theorem 2.1 in the selected source paper.

These are established external theorems, not conjectured inputs.

## Reciprocity argument

- The ideal E bounds the total coordinate sum, giving boundedness.
- The weighted Minkowski sum includes an origin in every projected simplex.
- Threshold support functions establish the equality of this sum with all
  ideal inequalities, including those of disconnected ideals when slack>0.
- Integer Minkowski coefficients give an integral polytope; an unproved
  integer-decomposition property is not being assumed.
- Positive capacities and positive slack make the all-ones vector strictly
  feasible and establish full dimension.
- Every nonempty ideal inequality has a nonzero normal. Redundancy does not
  invalidate the characterization of interior points by strict inequalities.
- Integer strictness lowers the scalar slack by exactly one.
- Subtraction of the all-ones vector lowers each element's capacity by one.
- For fixed positive integer parameters, the lattice polynomial restricted
  to their ray is the ordinary Ehrhart polynomial, including at negative
  arguments by polynomial identity.
- Extension from positive integer tuples to all parameters is algebraic;
  no reciprocity is applied to a degenerate zero-parameter polytope.

## Consequences

- In the falling-binomial derivation, a0+sum(ae)=n, so all signs cancel the
  external factor (-1)^n. This cancellation does not use even n.
- The s=0 specialization retains exactly the vectors of coordinate sum n.
- Maximality is proved by unions of tight ideals, not assumed from purity.
- Word contents are bases for the dual preorder. Complementing filter bounds
  gives the required lower-ideal content bounds for the original preorder.
- Equal-level letters are sorted decreasingly. Required strict level jumps
  occur at non-descents (including equal adjacent letters), giving the
  exponent n-1-des rather than des or asc.
- The ordinary zeta convention is Z(P,k+1)=number of k-entry multichains.
  Thus Z(P,-1) corresponds to Ehrhart evaluation at -2, not at -1.
- The source already identified the implications to the word and ordinary
  zeta conjectures. Those implications are not claimed as new discoveries.

## Matrix and heterogeneous duality

- Copy multiplicities p on the left and q on the right are independent.
- Add one universal root to each side. Retain the left-root neighborhood,
  but give its full-simplex summand coefficient zero.
- All other simplex coefficients are one, so each term in Postnikov's sum
  is exactly one, including the root's factor.
- The draconian coordinate sum is |q|, not |p|.
- Non-root subset neighborhoods are {right root} plus q(U(S)) vertices.
- Subset inequalities and filter inequalities are proved equivalent even
  when some labels have zero left or right copies.
- The root coordinate is the unique nonnegative slack determined by the
  filter E; it introduces no extra multiplicity.
- Reversing the order converts filters into ideals and swaps p and q.
- Multichain increments give C_tau(ell*1,k*1), in that order.
- The empty-chain/zero-dilation cases both count one.

## What was checked computationally

All reflexive relations through n=4 were generated, then tested for
transitivity. For each of the 389 retained labeled preorders, direct
inequality counts, rising and falling formulas, a whole double-polynomial
reciprocity identity, actual interior-point sets, maximality, word
histograms, zeta evaluation, and a finite matrix block were compared.
Heterogeneous cases were seeded parameter tests rather than exhaustive.
See the machine-readable output for exact counts.

## Boundaries of the claimed results

No external peer review; no Lean or other proof-assistant certification.
No complete priority certification.
No proof of full q-zeta reciprocity, shellability, magic positivity,
real-rootedness, gamma-positivity, or the support-polynomial conjectures.
No canonical direct bijection between the two colored-array sets is supplied.
No new general graph-duality theorem is claimed: the contribution is the
preorder encoding and its weighted consequences.
