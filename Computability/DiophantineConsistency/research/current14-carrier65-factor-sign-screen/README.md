# Factor-sign circuit screen

No operation reduction survived this bounded screen of 15 sign variants of
the current 65-gate graph. This is not a global lower bound, a general
zero-set search, or a new Lean theorem.

The four subtraction factors `N0`, `N1`, `Nt`, and `scaled_Ns` each have
one use: they enter the final multiplication chain. For each nonempty subset
of those four factors, swap the operands of its subtractions. An even number
of sign changes leaves the output polynomial unchanged. For an odd number,
also replace the final subtraction by addition: the resulting output is the
negative of the original polynomial, with exactly the same zero set. These
identities hold over every commutative ring. The checker validates the source
rows and sole-consumer structure, then performs 30 modular full-graph
comparisons per variant as controls. Every variant retains 65 live gates.

On each variant, the pinned functions from
`../current14-carrier65-integer-leaf-superopt/` screen the same one-target,
source-order-preserving replacements with one arbitrary new fixed integer
leaf: aliases, affine forms, `(x+c)*y`, `(c-x)*y`, `x*y+c`, and
`c*(x*y)`. Earlier nodes and 0–4 are available, and liveness counts gates
only. Four positive-witness samples at each of three verified primes filter
each form. Integer constants reduce modulo every prime, and no nonliteral or
per-prime sampled scale was unresolved. As before, modular survivors would
need exact symbolic proof.

There were no strictly smaller live circuits in either search on any of the
15 variants. Constructed affine and factored positive controls each reduce
three gates to two. The screen pins the current graph and both inherited
screen source functions, authenticates all four fixed port payloads, and
records complete per-variant counts in [result.json](result.json).

This tests the listed sign subsets plus **one** local exact-target rewrite.
It does not test arbitrary simultaneous rewrites, other zero-set
equivalences, other circuit forms, or operation minimality. The earlier
six-pair source and receipt are retained as `six-pair-prior-screen.py` and
`six-pair-prior-result.json`; they are not the final result. No Lean,
native replay, or PDF interpretation runs.
The independent external review is in
`../../reviews/current14-carrier65-factor-sign-screen-independent/`.

From the DiophantineConsistency directory:

```sh
python3 -I -S -B research/current14-carrier65-factor-sign-screen/screen.py > /tmp/carrier65-factor-sign.json
cmp /tmp/carrier65-factor-sign.json research/current14-carrier65-factor-sign-screen/result.json
```
