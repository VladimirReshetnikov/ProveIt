# Two local moves around the complete 86-operation polynomial

The [checker](complete86_two_move_scout.py) and [receipt](complete86_two_move_scout.json)
extend the pinned [affine-port search](complete86_affine_port_scout.md) by one
additional local move. They enumerate **66,673 distinct complete circuits**
reachable by at most two moves after exactly six joint main/input-root
schedules. The minimum remains **86=48M+38A**, attained by 2,661 sources.
The multiplication/addition Pareto frontier also contains only `(48,38)`.
This is a bounded negative search result, not a circuit lower bound or a
new universal construction.

## Exact search boundary

The starting polynomial is the normalized form of the frozen
[first-root construction](complete86_factored_first_root.md). It has nineteen
positive witnesses, ordinary input `x`, six supplied fixed-program numeral
ports and exact degree 179. Every emitted candidate retains the entire
polynomial and all these ports. Its output is the complete polynomial
represented by the original eight-factor product minus one; local moves
may change the literal final product gates.
No witness is replaced by a weaker coordinate and no equation is discarded.

The six seeds are exactly those in the preceding affine-port report:
the original schedule; left and right distributed root schedules; two
schedules expressing the main root through the input root; and the schedule
recovering the rho product from the combined and sigma products. Their
twelve root identities are checked by exact coefficient expansion.

At one reachable gate, a move may reassociate signed addition/subtraction,
reassociate multiplication, distribute multiplication over addition or
subtraction, factor a shared immediate operand, or exchange a difference
of literal squares with a conjugate product. The preceding report specifies
the exact operand permutations, allowed signs, and handling of a lone term
as a product with one. The same authenticated implementation is used here;
this author search does not claim an independently implemented grammar.

The first layer contains all six seeds and all their one-move outputs.
It reproduces the predecessor's 1,300 move instances and 874 distinct
complete sources. Every source in that first layer then receives every
allowed local move once. The union includes the zero-, one- and two-move
cases. There is no gate-cost cutoff, beam selection, or further recursive
closure. Thus an intermediate cost increase within these two moves is
allowed; sequences needing three or more moves are outside the census.

Exact commutative common-subexpression reuse, integer constant folding,
zero/one identities, and dead-gate pruning apply to each entire graph.
Binary `0-x` remains paid. The same canonicalization leaves the original
at 86 operations. Equality of distinct graphs means equality after this
specified canonicalization; it does not identify every pair of
algebraically equivalent circuits.

## Full-source results

| Complete operations | Distinct complete sources |
|---:|---:|
| 86 | 2,661 |
| 87 | 13,366 |
| 88 | 24,249 |
| 89 | 19,145 |
| 90 | 6,460 |
| 91 | 792 |
| **Total** | **66,673** |

There are 192,823 second-move instances and 17,548 distinct second-move
cut identities. All first-move cut identities already occur in this latter
set. The twelve seed identities are additional. Every unique complete
source is emitted, checked for literal closure and live gates, and recounted
by operation kind: **5,882,977 paid gate occurrences** in total. The full
free-port list must equal that of the baseline, including every fixed
numeral port. Every distinct graph must also emit a distinct source packet.

The receipt records the complete cost and M/A histograms, all 2,661
minimum-source hashes, deterministic census digests, and one complete
source for each distinct M/A ledger. Its route records name the starting
seed and local substitutions. These are replay descriptors with node IDs
and immediate expressions, not standalone expanded cut certificates: the
full deterministic replay reconstructs their dependency graph and proves
the cuts. The saved source representatives themselves are complete paid
polynomials, not isolated arithmetic fragments.

## Polynomial proof and computational scope

For each distinct local substitution the checker compares exact sparse
coefficient expansions at its declared cuts. Structurally dependent cuts
are expanded as in the pinned grammar implementation. Seed identities,
local identities, and the stated emitter identities compose inductively
to prove equality of the entire polynomial over any commutative ring.
Every candidate therefore inherits the parent's exact degree 179 and its
full positive zero set on unchanged coordinates. No new positivity
argument or compiler theorem is needed for these all-value identities.

One deterministic signed-integer and one rational full evaluation of
every distinct source provide 133,346 additional output checks. They
supplement the exact identities; they do not establish them and do not
materialize a universal halting witness. The helper authenticates both
predecessor trios and executes only graph, grammar, coefficient-proof,
source-validation, and evaluation primitives from the affine helper.
Neither its historical verifier nor the older 292,320-choice
strong/auxiliary census is invoked.

The result covers no new affine coordinate, arbitrary linear circuit,
unit-premise simplification, or unbounded rewrite sequence. In particular,
the separate complement-coordinate and independent-gamma questions are
not decided by it. The established bounds remain **74 certificate
operations / 86 polynomial operations**, with the existing degree frontier
unchanged.

## Reproduction

Only Python's standard library is required. From any working directory:

```sh
python /path/complete86_two_move_scout.py \
  --root /path/to/native-stream-queue \
  --expect /path/complete86_two_move_scout.json
```

Use `--output FILE` to write a fresh receipt. The source hash is recorded
in the receipt, predecessor source/proof/receipt pins are strict, optimized
Python is rejected, and saved-receipt equality is recursively type-sensitive.
This is a standalone research CLI, not a general hostile-packet compiler API.
