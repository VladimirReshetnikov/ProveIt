# Bounded one-new-integer-leaf circuit screen

No strictly smaller circuit survived this bounded screen of the maintained
65-gate graph at its actual current integer ports. It does **not** establish a
global minimum, exclude arbitrary coordinated rewrites, or prove anything
about a change that preserves only the positive zero set. The displayed
equation and all previous candidates are unchanged.

The screen extends the existing
`../rational-carrier64-affine-leaf-screen/` engine to the current 65-row
integer-leaf graph and adds factored forms. Unlike that earlier experiment,
the fixed ports are the actual current four integers and the one additional
constant may be **any fixed integer**, including a new precomputed combination
of those ports. Its construction, bit length and storage are not charged;
binary `+`, `-` and `*` cost one, and all fixed integer leaves are free.
The corrected liveness routine counts reachable binary gates, not leaves.

For one target row at a time, earlier nodes and literals 0–4 are available.
The enumerated replacements are a fixed constant or earlier-node alias;
`x+c`, `c-x`, `c*x`; `c*x+y`, `c*x-y`; `(x+c)*y`, `(c-x)*y`;
`x*y+c`; and `c*(x*y)`, with one free integer `c`. Commutative variants
and subtraction of a constant are represented by these forms. A replacement
must equal the original target for all positive inputs, and the unmodified
suffix must then have fewer than 65 live gates. The screen considers one
replaced target, not coordinated changes to multiple rows.

It evaluates four deterministic positive-witness samples at each of three
verified primes. At each prime the possible `c` residue is inferred and
checked against the other samples. An actual integer coefficient has a
well-defined residue at every prime, so an identity in an enumerated family
cannot be discarded by these samples; a modular survivor would still need
an exact symbolic proof. No sampled scale was unresolved or identically zero
for a nonliteral input. The port files are checked against both their raw and
compressed SHA-256 hashes.

All 65 targets were screened. The affine part checked 431,860 two-gate
queries; the factored part checked 431,860 `(x+c)*y`/`(c-x)*y`, 219,505
`x*y+c`, and 212,420 `c*(x*y)` queries. There were 116 affine and 342
factored modular survivors before the liveness test; none reduced the
reachable gate count. Two constructed controls, one affine and one factored,
were reduced from three gates to two.

This excludes only these exact-target, source-order-preserving local families
at the fixed ports. It does not cover more than two new gates, more than one
new constant, other two-gate shapes, changing existing nodes together, a
rewrite valid only on graph zeros, a positive-witness reparameterization, or
global arithmetic-circuit lower bounds. The screen does not run Lean or
establish the existing endpoint's provider ancestry.
The independent external review is in
`../../reviews/current14-carrier65-integer-leaf-superopt-independent/`.

From the DiophantineConsistency directory:

```sh
python3 -I -S -B research/current14-carrier65-integer-leaf-superopt/screen.py > /tmp/carrier65-integer-leaf.json
cmp /tmp/carrier65-integer-leaf.json research/current14-carrier65-integer-leaf-superopt/result.json
```
