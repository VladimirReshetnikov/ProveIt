# Additional reduction audit: reachable guards and pulse synthesis

This package supplies **no machine below 246 states**. Its positive result is
an independently checked invariant for the original numerical program from
every six-nonformula safe root. Its negative results delimit two concrete
search methods; they are not state lower bounds.

## Source and attribution

The program is Mira-Cult's program, verified by Jeff using Wade's compiler
framework and preserved by ProveIt. `reference/Prog254.v` has SHA-256
`1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746`.
The transition source is the incoming context246 artifact, incorporated in
ProveIt revision `8cdc55ff9281b0aaba49bf74b0b225d57f12b893` as
`docs/incoming/zfc-context246-20261018.zip`. Its extracted original-label table
has SHA-256
`303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee`.
The attribution and ProveIt license supplied with that artifact are retained
under `reference/`. The new analysis, verification, and search programs were
written in this investigation on 18 October 2026. The generator's literal
source parser is ported from the inherited context246 rebuild script.

The six guard exclusions were already known for the earlier zero-root
investigation. This check independently extends their finite certificate to
all roots with `T=W=H=0` and arbitrary `N,A,D,X,Y,L`. The correct logical order
throughout is `N,T,W,A,D,H,X,Y,L`.

## The inductive certificate

The finite source has 6,459 internal decoder nodes and 6,460 instruction
leaves. At an instruction leaf, increment, guarded decrement, break and
continue update the program-counter word exactly as in the source. The next
leaf is decoded with a zero suffix. The verifier retains cleared carry zeros
and checks that decoding never discards a nonzero suffix.

Each natural-valued register is classified into `{0}`, `{1}`, or `{2,3,...}`.
A mask uses bits 1, 2 and 4 for these respective categories. The initial masks
are

```text
[7,1,1,7,7,1,7,7,7].
```

Increment sends category0 to1, category1 to2, and category2 to2. The zero
decrement branch requires category0 and preserves it. The positive decrement
branch sends category1 to0 and category2 to either1 or2. These rules are sound
for every natural value. Joining masks by union is an overapproximation.

`certificates/product-invariant.json` gives nine masks at each leaf, or `null`
for an unreachable leaf. `verify_invariant.py` reparses the literal source,
checks that the initial masks are included, and checks every feasible abstract
successor against its destination masks. It does not run the generator's
worklist. Induction on the number of numerical instructions then proves that
every actual run from a stated initial root stays inside these masks.

The certificate excludes exactly these six guarded cases, using zero-based
indices in depth-first leaf order with the zero branch first:

| Index | Instruction path | Operation | Excluded branch |
|---:|---|---|---|
| 8202 | `111010010110001100` | decrement X | positive |
| 8203 | `1110100101100011010` | increment H | entire instruction |
| 8204 | `1110100101100011011` | continue 2 | entire instruction |
| 8358 | `111111000` | decrement T | positive |
| 8359 | `1111110010` | increment X | entire instruction |
| 8360 | `1111110011` | continue 2 | entire instruction |

There are 6,456 admitted sites, 8,385 feasible guarded cases, and 8,384 feasible
nonhalting edges. These exclusions free no new literal transition row: the
full and restricted affine instruction audits both use the same 472 literal
state/read pairs. That last statistic was checked in the main investigation;
the small standalone verifier here checks the numerical invariant only.

## Stronger finite abstractions did not exclude additional guards

The compact product analysis was refined by classifying every exact value up
to 2, 3, 4, 8, 16, 32 and 64 separately, with one remaining class for larger
values. Each produced the same six exclusions. The corresponding diagnostic
summary is in `results/refined-guards-summary.json`; those larger product
certificates are not retained here.

The relational certificate retains whole vectors of nine categories, rather
than taking nine independent unions. It starts with `N,D>=2` and all other
registers zero, which contains the exact context246 root with `N=D=3`. Its
compressed bitsets admit 7,725,633 leaf/vector pairs. Independent verification
checks 8,669,994 abstract successor edges, and again excludes exactly the same
six guards. The certificate is
`certificates/disjunctive-invariant-3.zlib`.

This finite result does not rule out arithmetic invariants such as relations
between register values or invariants expressed at larger program phases.
Neither verifier is a Lean or Rocq kernel endpoint.

Run the independent checks with Python 3.10 or later:

```sh
python3 -B verify_invariant.py
python3 -B verify_invariant.py --relational
```

The relational check takes substantially longer than the product check; its
recorded run took about 43 seconds. Assertions are part of the verification,
so `-O` and `-OO` are rejected.

The worklist generators are also supplied under `generators/`. They compute
the product invariant, the full-vector invariant, and the refined-product
diagnostics. Their output directory must be specified explicitly, and they
refuse to overwrite any existing output file. For example, from this package:

```sh
python3 -B generators/reachable_guards.py --output-dir /tmp/zfc-product-recomputed
python3 -B generators/disjunctive_guards.py --output-dir /tmp/zfc-relational-recomputed
python3 -B generators/refine_guards.py --output-dir /tmp/zfc-refined-recomputed
```

The full-vector generator computes abstract graph reachability by a worklist;
the independent verifier checks initial inclusion and closure, without
separately establishing that the supplied set is the least fixed point.
The portable generator entry points were smoke checked by parsing the source
and constructing all 8,391 guarded CFG edges. These agree with the independent
verifier's graph. The original full worklist results are retained; the full
worklists were not rerun after porting. See `generators/README.md` and
`results/generator-port-smoke.json` for scope and reproduction details.

## Three/four-row pulse-controller synthesis

The second experiment deletes old state255 and treats selected retained rows
as unknown. Every unknown row chooses its write bit, direction, and successor
from 25 explicit retained runtime states, giving 100 possible actions per row.
The four three-row families each contain 1,000,000 complete assignments. The
four-row family, freeing both rows of old75 and old131, contains 100,000,000
assignments. These are sizes of finite recipe spaces, not counts of separately
simulated complete tables; lazy branching prunes families at first failure.

Each assignment must satisfy 48 complete-tape register-macro fixtures. The
fixtures cover increment, positive decrement and zero decrement at four
selected registers, with four primary vectors and one or two spare blocks.
All spares have value1 in the main lane. This is a valid stronger recurrent
invariant of context246: its bootstrap has 167 value1 spares, increment
appends another, and other instructions preserve the suffix.

The required endpoint includes the exit state, head position and entire tape;
all other cells are blank. The synthesis accepts a fixture only if its
endpoint is reached at a tested tick from1 through249. At most250 transitions
are executed per partial check. Thus a recipe requiring a longer macro is
outside this experiment. No finite success would by itself prove an unbounded
register contract.

For the all-value1-spare lane, the four three-row families require respectively
16,821, 13,221, 48,848 and 28,313 partial trace checks. The four-row family
requires 772,207. No recipe survives all fixtures. The separately tested lane
with four more general sampled spare patterns also has no survivor; the
four-row count there is 690,607 partial trace checks.

The portable reproduction script checks all 48 baseline fixtures first,
then runs the five searches:

```sh
python3 -B search_pulse.py --baseline-only
python3 -B search_pulse.py
python3 -B search_pulse.py --arbitrary-spares
```

The search uses only the literal table and Python's standard library. It
reports its finite bounds explicitly. It does not establish that state255
is essential, that 246 is minimal, or that no smaller implementation exists.
