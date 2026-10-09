> Maintained continuation: the production spin backend now defaults to exact
> binary valuation arithmetic, adapted from the certified-primitives report in
> commit `bc5b91385`. The historical measurements below precede that transfer.
> See the synthesis valuation chapter and `benchmark_spin_valuation.py` for
> the current comparison; `arithmetic="shifted"` retains the old representation.

# Exact Jones computation with two edge orientations

`fastunknot/spin_jones.py` computes the full Jones polynomial, or decides
whether that polynomial is one, using a binary orientation on each frontier
edge. With local caps disabled, its default certified crossing order gives
`poly(n) * 2^O(sqrt(n))` deterministic bit complexity on every validated
classical knot diagram. This improves the previous maintained faithful Potts
backend's `poly(n) * 2^O(sqrt(n) log(n+1))` bound. It is an invariant-computation
bound. A Jones polynomial equal to one remains inconclusive for recognition.

This asymptotic bound is already known in the literature. In particular,
Clément Maria's [2021 SoCG paper](https://doi.org/10.4230/LIPIcs.SoCG.2021.53)
establishes stronger general quantum-invariant results with bit-cost
accounting. The present contribution is a checked realization in this
repository, including a drawing-free turning construction, exact integer
encoding and independently audited integration. No priority claim is made
for the general Jones bound.

## Interface

```python
from fastunknot import Diagram
from fastunknot.spin_jones import spin_jones_exact, verify_turn_certificate

diagram = Diagram.from_braid(3, [1, -2] * 5)
result = spin_jones_exact(diagram, include_polynomial=True,
                          max_states=None, max_transitions=None)
assert verify_turn_certificate(diagram.pd, result['turn_certificate'])
print(result['jones_polynomial'])
```

The defaults retain 4,096 states and 200,000 transitions. `SpinLimit`, a
`FilterLimit` subclass, records local exhaustion; a caller's global check
exception propagates. No unfinished scalar or polynomial is published.
An independently completed separator certificate can survive later scalar
exhaustion in `statistics`. These caps count represented states and compiled
tensor transitions, not bytes or elementary bit operations.

`certify_order=False` evaluates a supplied order directly and has the bound
`poly(n) * 2^O(w)` for its actual maximum frontier `w`. The number of states is
at most `2^w`; the wider deterministic operation envelope also covers Python
dictionary collisions. A collision-free table implementation obtains
`poly(n) * 2^w`. The default considers the ordinary greedy order even when an
initial order is supplied, then constructs and verifies the existing planar
separator certificate.

Raw results retain integer `scaled_bracket` and `unknot_scaled_bracket`.
`witness_from_spin` converts these to signed hexadecimal strings in a
nontrivial-polynomial witness. Full polynomial coefficients are already
hexadecimal. Neither this module nor its tests change Python's process-global
decimal integer-conversion limit.

## Exact algebra

For the face permutation `phi = sigma * alpha`, every face corner turns by
minus one quarter turn. The certificate supplies antisymmetric integers on
directed edges whose sum around a bounded face is its degree minus four and
whose sum around the selected outer face is its degree plus four. A dual-tree
circulation solves these equations in linearly many records, each containing
`O(log n)` bits. The independent verifier revalidates the PD and checks the
face equations without replaying the solver.

The equations imply that each oriented smoothing circle has total quarter
turn either four or minus four. Put `A = B^2` and `t = z B`, where `z^4 = -1`.
Summing the two orientations of a circle gives
`t^4 + t^-4 = -A^2 - A^-2`, exactly the bracket loop factor. Multiplying every
crossing tensor by `B^4`, and each directed-edge factor by `B^abs(b_e)`, removes
negative integer exponents. A fixed boundary orientation determines one
`z`-coordinate; the code checks this fact at local assembly and at every
coefficient merge. Scalar multiplication uses binary shifts and additions.

Choosing `B = 2^ceil((2n+2)/8)` gives `X = B^8 >= 4 * 4^n`. The standard bounds
`sum(abs(Jones coefficients)) <= 4^n` and degree magnitude at most `2n` make
evaluation at `t = X^-1` injective on the required polynomial class. Exact
normalization followed by balanced base-`X` decoding recovers every
coefficient. The sum of absolute cochain turns is `O(n^2)`, so intermediate
integers have polynomial bit length despite the input-dependent evaluation.
Before its identity shortcut, the decoder independently checks the exact
normalization prescribed by the crossing count, writhe, scaling and base. Its
two-set-bit form permits this check without rebuilding a large integer; a
forged huge shift is rejected from its bit-length mismatch before allocation.
The decoder still presumes that the supplied scalar came from the exact
query, and is not an independent verifier of the whole state sum.

## Verification

```sh
python -m unittest discover -s tests -p 'test_spin*.py' -v
```

The nine focused kernel/order tests cover 140 comparisons with an independent
whole-cube
Laurent oracle on real knots, mirrors, random crossing orders and different
outer faces; direct quarter-turn sums for every oriented smoothing circle on
small diagrams; forged-certificate rejection; twenty random vertex gauges;
180 signed bounded-polynomial decoding cases; exact budget boundaries;
cancellation; the crossing-free knot; and large JSON-safe exact scalars. The
decoder checks include forged equal scalars and cancellation before its
identity shortcut. Four further integration tests cover CLI and recognition
behavior. The
supplied-order regression uses the exact shuffled 64-crossing grid that
exhausted the initial policy's state cap.

## Performance evidence and retained failed policy

```sh
python -B benchmark_spin_jones.py --output results/spin_jones_local.json
python -B benchmark_spin_jones.py --only grid-8-shuffled \
  --output results/spin_jones_seed_followup_local.json
```

The retained initial audit contains 490 measured queries in seven shuffled
rounds, plus 70 excluded warmups, on fourteen inputs. Its five arms compare
two identical faithful-Potts controls, the new default spin query, and both
algorithms on one common certified order. Every completed arm returns the
same full polynomial. Default-query timing includes fresh diagram construction
and all ordering; matched-order timing excludes the shared order construction
and includes every other query cost. Small cases use the independent cube
oracle. Larger grid examples have separately verified descending presentations.

The initial 144-crossing grid improves from median 313.118 ms to 186.080 ms in
the default scope, with median paired ratio 1.719. On a common order, medians
are 274.913 ms and 145.532 ms, with median paired ratio 1.814. Potts retains
877 peak states and 48,386 transitions; spin retains 240 states and 32,098
transitions. The 196-crossing grid completes all seven spin runs with 480
states and 89,122 transitions, while all corresponding Potts runs exhaust
the 4,096-state cap. This last comparison is a capacity result, not a speedup
against a completed Potts query.

Several small inputs and both tree medials regress substantially. On the
254-crossing tree medial, median faithful-Potts/spin times are 66.662/305.133
ms. Consequently this backend remains optional.

The first policy omitted the greedy candidate when the caller supplied an
order. On a shuffled 64-crossing grid this caused seven state-cap failures.
That source and driver are preserved in `initial/`, with their matching
SHA-256 records in `../results/spin_jones_initial_20261008.json`. The repaired
policy compares the supplied and greedy orders before separator certification.
A focused follow-up retains all 35 measured queries plus five warmups in
`../results/spin_jones_seed_followup_20261008.json`: every arm completes.
Default-query medians are 19.293 ms for Potts and 14.625 ms for spin; common-
order medians are 3.963 ms and 10.790 ms. The default-query gain on this input
comes from ordering policy, while its matched-order contraction still loses.
The two timing runs are retained separately and should not be pooled.
Their measured implementation predates the additional normalization
consistency check; the exact source matching the later run is preserved in
`before_normalization_validation.py`. The invariant algorithm, state counts,
and transition counts are unchanged by that subsequent defensive check.

These measurements concern exact full-Jones queries. Cheap descending or
structural certificates already recognize several benchmark unknots; the
invariant gains do not by themselves imply full-recognition speedups.
