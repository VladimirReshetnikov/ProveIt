# Shared norm terms after cancelling Δ

The existing unscaled candidate is a zero-preserving change on the same 14
positive inputs, but it uses **66 integer-leaf operations**, one more than the
maintained equation. A bounded search of a natural way to share its two norm
monomials found no saving. This does not rule out a different 65- or 64-gate
zero-equivalent equation or any general arithmetic-circuit optimization.

Write `d = Δ`, `c2 = c²`, `t = d*i²*c2²`, `g = V²-y²`, and let `A` be
the product of the three remaining factors. The maintained and unscaled
polynomials satisfy the identity

```
old = A * (d*t*g + y²) * (d*f² - d*t) - d
    = d * (A * (d*t*g + y²) * (f² - t) - 1).
```

This holds over every commutative ring. For the current positive-input
equation, `d = a² + 4a + 3 > 0`, so cancellation in the integers gives the
same zero set with the identity map on all 14 inputs. The parent and existing
unscaled source share the first 51 literal gates; their complete suffixes are
independently evaluated in an exact sparse polynomial ring and checked against
this identity. The existing unscaled graph has exact degree 138 according to
its separate certificate, versus the maintained degree 150, but the extra
gate means it is not the requested operation reduction. Its all-model and iPRA
syntax transfer remains a separate proof obligation.

The bounded search assumes that `d`, `i`, `c2`, and the already needed shared
`d*c2` are available and that both `t = d*i²*c2²` and `d*t` must be built
using multiplication alone. It enumerates every binary multiplication tree
for both monomials, merges identical monomials between the two trees, and
minimizes their union. The minimum is four new multiplication gates; one
witness is `i*c2`, then `i²*c2`, then `t`, then `d*t`. There are 20 and 67
subset-minimal individual tree circuits and 1,121 distinct pairwise unions.
The maintained scaled tail instead needs two gates for its shared square and
one for `d*f²`; this restricted normalization thus costs one extra gate.

The enumeration permits commutative reassociation and common-subexpression
sharing within these monomial trees. It does not include addition or
subtraction inside their construction, cancellation-based arithmetic
circuits, changing the shared `d*c2` computation, eliminating either norm,
changing several higher-level factors together, arbitrary reparameterization,
or zero-set equivalences other than the displayed exact factorization. It
therefore is not a lower bound for the full equation. In particular, the
fact that each factor is a unit at a zero does not by itself justify deleting
the auxiliary factor.

Reproduce this read-only check from the DiophantineConsistency directory:

```sh
python3 -I -S -B research/current14-carrier65-unscaled-tail-search/search.py > /tmp/carrier65-unscaled-tail.json
cmp /tmp/carrier65-unscaled-tail.json research/current14-carrier65-unscaled-tail-search/result.json
```

The program pins both current and unscaled source graphs. It runs no Lean
process, native proof replay, or PDF interpretation.

Independent review, including a separate bounded multiplication-DAG search,
is in `../../reviews/current14-carrier65-unscaled-tail-search-independent/`.
