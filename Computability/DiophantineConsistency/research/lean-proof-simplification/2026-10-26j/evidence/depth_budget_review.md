# Independent review: DepthBudget mechanism prototype

Reviewed files:

- `output/new-lean-simplification-2026-10-26/lean/DepthBudget.lean`
- `ProveIt/Computability/DiophantineConsistency/Lean/DiophantineConsistency/BoundedForallDepth.lean`
- `ProveIt/Computability/DiophantineConsistency/Lean/DiophantineConsistency/RepresentationSize.lean`

## Finding

The two plan shapes and all charges match the source depth proofs. The
prototype establishes a valid generic upper-bound mechanism. It does not yet
prove a shorter version of either project theorem: the supplied `Covers`
assumption is precisely the missing connection to the real `GraphRep` data.
Its comments already acknowledge that limitation. It should be labelled
“compiled generic mechanism; source adapter pending.”

## Exact correspondence

`RepresentationSize.GraphRep.depth_add_le` and `depth_mul_le` charge 6
over a common upper bound. `BoundedForallDepth.pow_depth_le`,
`binomial_depth_le`, `sub_depth_le`, `mod_depth_le`, and `div_depth_le`
charge 8 and require a floor of 512. `factorial_depth_le` charges 6 and
requires a floor of 16384. These are the prototype's four plan constructors.
Source lemmas sometimes write `6+h` rather than `h+6`; commutativity is
the only adapter arithmetic needed there.

For factorial, offsets from base 512 are:

| Source node | Offset |
| --- | ---: |
| `n`, constants | 0 |
| `shift = n+2` | 6 |
| `radius = shift^shift` | 14 |
| `radius+n` | 20 |
| `c = binomial(radius+n,n)` | 28 |
| `radius+1` | 20 |
| `(radius+1)^n` | 28 |
| `c-1` | 36 |
| numerator | 42 |
| numerator divided by `c` | 50 |

Thus `512+50=562`, exactly the intermediate ceiling already reached by
the source's `hlast`; the existing public theorem then weakens it to
16384. This is not a new sharper bound. It is a more declarative way to
derive the same bound.

For product, offsets from a base at least 16384 are:

| Source node | Offset |
| --- | ---: |
| `rn`, `rt`, constants | 0 |
| `rn+1` | 6 |
| `(rn+1)*rt` | 12 |
| previous plus 1 | 18 |
| previous to power `rn` | 26 |
| `q` (previous plus 2) | 32 |
| `rt^rn` | 8 |
| `rn.factorial` | 6 |
| `q+rn` | 38 |
| binomial of previous and `rn` | 46 |
| factorial times binomial | 52 |
| first numerator | 58 |
| `rt*q` | 38 |
| denominator `rt*q-1` | 46 |
| final remainder | 66 |

The plan `arithmetic` deliberately collapses pow/binomial/sub/div/mod
because their depth interfaces have identical floors and charges. It
does not assert that their denotations or actual depths are equal.

## Why the generic theorem is sound

`required` is an upper bound for every local floor. `extra` is the
maximum accumulated charge on a plan path. If children satisfy
`depth ≤ base+extra` and every floor is at most `base`, the local
`max` bound is at most `base` plus the largest child extra. Adding
the local charge proves the parent bound. The induction on `Covers`
is exactly this argument. No additional assumption about the supplied
program's syntax is hidden in the arithmetic theorem.

The prototype's description “never syntax trees” is too broad:
`Plan.required` and `Plan.extra` recurse over the plan tree. More accurate
wording is “does not expand the represented polynomial or graph syntax.”

## Integration required before a source-saving claim

1. Derive one local adapter per real constructor from the existing depth
   lemmas, giving bounds such as
   `depth(r.add s) ≤ max depth(r) depth(s) + 6` and
   `depth(r.pow s) ≤ max 512 (max depth(r) depth(s)) + 8`.
   The old common-bound API can supply these by taking that displayed
   maximum as `h`; this needs no expansion of expression fields.
2. Generate the `Covers` derivation from the actual constructor expression,
   or use a tactic which recursively applies those adapters. A hand-copied
   plan plus a manually expanded `Covers` proof merely moves the original
   intermediate arithmetic to a second representation and risks drift.
3. Retain graph input depths as premises, prove constant/coordinate inputs
   at depth 1, and keep reindexing as a depth-preserving adapter. The plan
   input case itself does not mean graph leaves have depth zero.
4. Preserve sharing of repeated subgraphs (e.g. `q` and `radius`) in generated
   proof terms. A recursive tactic that unfolds all let-bound subgraphs may
   duplicate the expensive proof object even while shortening source text.
5. `finiteRep_depth_le` is not implemented by this file. It additionally
   needs conjunction (+2), finite-all (+2 per index), reindexing (0),
   and the distinct fixed floors for congruence/divisibility. Treat it as
   a later client, not a currently checked result.

The actual gain is elimination of hand-maintained intermediate ceilings,
`.trans (by omega)` coercions, and `h1`…`hN` names, without expanding the
underlying polynomial. The approach is standard compositional upper-bound
reasoning applied to a new concrete proof family. It is distinct from the
audited earlier suggestions about polynomial weighted degree, coefficient
majorants, moving witness-count projection lemmas, and sum-expression cost.
No whole-project reduction, compiler speedup, or net line saving follows
from the mechanism prototype alone.
