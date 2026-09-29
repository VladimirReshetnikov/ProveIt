# Proof audit and verification boundaries

## Universal reduction

Composition is ordinary function composition. A word containing the singular
letter is decomposed at its **rightmost** singular occurrence as `u s p^j`.
It identifies the translated pair `p^(-j)(x), p^(-j)(y)`. The full cyclic
edge orbit contains these inverse translates, so all such colorings are
improper. This direction of composition is essential.

A same-cycle collision produces cycles of length `m/gcd(m,e)`, with a
2-cycle treated as a single undirected edge. Its four-color count is still
`3^2+3=12`. A cross-cycle collision gives `gcd(a,b)` bicliques by the
Chinese remainder criterion. Remaining states are isolated; their factor
`4^r` is retained.

Both-singular and both-permutation regimes are treated separately. Missing
output colors are covered explicitly, so no surjectivity hypothesis is
hidden in the universal upper bound.

## Period estimates

The finite certificate subtracts `m J(r)` or `lcm(a,b) J(r)`, not an
incorrect product of unrelated coloring periods. These are conservative
upper bounds on the permutation order. `J(0)=J(1)=1`. The period bound can
be loose, but every comparison remains strict away from the desired pair.

## Large-n argument

The cross-cycle cases with repeated components or isolated states have
proper-coloring count at least `9*2^n`, and the permutation order is less
than `2^n`. A same-cycle obstruction has deficit greater than `7*2^n`.
The optimal candidate has deficit less than `7*2^n` for `n >= 26`, using
`40*3^13 < 2^26` and a decreasing ratio.

Only a full coprime two-cycle graph remains. Strict decrease under balancing
comes from the exact finite difference of `g(t)=4*3^t-12*2^t`, plus the
strict improvement in the product term. The nearest-coprime formula is
proved separately, including the `n = 2 (mod 4)` offset-two case.

## Finite proof component

The proof for `7 <= n <= 25` uses 2,059 tagged integer entries. This is an
exhaustive check of a proved finite list of necessary bounds, not a search
for likely witnesses. The minimum is unique in every row. Both checkers
compare the minimum, split, margin, and complete candidate count. The
independent checker also compares the runner-up tag and does not import
primary implementation code.

The larger sweeps through 200 and 100, respectively, provide regression
evidence but are not needed for the all-n proof once the analytic argument
is established.

## Attainment

The Holzer–König generation theorem is an explicit external dependency.
The manuscript proves the projected four-color orbit size inside that
monoid and proves accessibility and minimality of the displayed machine.
The breadth-first searches through 12 check those finite instances; they do
not prove the unbounded generation theorem.

## Rigidity and stability

Every collision can be chosen for the obstruction, so equality forces all
collisions to cross the same two optimal cycles. Two distinct cross pairs
remain distinct under permutation translation. A word containing the
singular map then has at least two monochromatic cross edges. Thus the
proper colorings and the exactly-one-edge colorings together contribute the
second-collision penalty; at most `ab` total exceptions can arise from
permutation powers. No properness assumption on the initial output is
needed for this penalty.

Equality in the one-collision bound forces all improper colorings and a
full-period proper orbit. Disjoint primitive palettes are necessary, not
sufficient; the manuscript gives an explicit accessible minimal counterexample
to sufficiency. Stability controls the cycle split, not distance between
transition tables.

## Enumeration and recurrences

The orbit inventory assumes coprime cycle lengths. Consequently divisors
`u | a`, `v | b` are coprime and each joint orbit has size `uv`; that division
would need modification without coprimality. The full-period count subtracts
one orbit, not one coloring, when describing an extremizer's missing set.

The three residue formulas are exact. The order-15 recurrence follows from
their periodic-exponential decomposition, not from fitting finite sequence
values. Its supplementary checks use exact integers. No minimal recurrence
order is claimed.

## Verification status

The delivered programs completed successfully. The PDF compiled without
LaTeX warnings and was rendered for visual inspection. Neither the human
proof nor the finite checker has been formalized in a proof assistant, and
there has been no independent referee review. These limitations are stated
in the manuscript and README.
