# Complete direct U15 polynomial in 536 operations

Combining the positive loader projection with shared controller sums reduces
the complete direct U15 ordinary-input polynomial from **611 to
536=219M+317A operations**. It has **87 positive witnesses, 31 comparisons,
and exact degree 1936**. The raw natural half-tape interface costs
**338=126M+212A operations**, with 51 positive witnesses and 11 comparisons.
This improves this complete direct tape construction. The separate universal
87-operation polynomial benchmark remains unchanged; its operation count is
not the new compiler's witness count.

| Interface | Certificate gates | Finalizer gates | Complete polynomial |
|---|---:|---:|---:|
| Natural raw half tapes | 306=115M+191A | 32=11M+21A | 338=126M+212A |
| Positive ordinary input, fixed valid program numerals | 444=188M+256A | 92=31M+61A | 536=219M+317A |

The [compiler](u15_packed_joint_affine536.py) and
[receipt](u15_packed_joint_affine536.json) emit both complete sources, all
comparison operands, the literal sum-of-squares finalizers, and exact source
identity certificates. Every binary addition, subtraction and multiplication
is charged, including multiplication by a fixed numerical coefficient.
Constants and copies are free. Every emitted gate reaches the final output.

## Two separately proved changes

The [downstream 561 compiler](u15_packed_downstream561.md), with its
[independent review](review_u15_downstream561.md), first removes 50 operations
from the ordinary 611 source:

- Four multiplications disappear by reusing already paid powers:
  `P^5=P^3*P^2` and `P^34=P^28*P^6`.
- One multiplication disappears by dividing both tape residuals by their
  literal factor two and sharing the single paid half-radix `32D`.
- Fifteen ordinary-loader coordinates have acyclic, strictly positive
  computed definitions. Their defining comparisons disappear, removing
  15 residual subtractions, 15 squares and 15 finalizer additions.

The positivity proof precedes every native typing or halting assertion. In
particular, the input radix is `q=x+input_slack>=2`; `Q=q^32` and
`B_in=2^31*Q` are positive; `J_in=B_in+index_beta` and
`P_in=(B_in-1)*J_in+1` are positive. Solving the parent congruence gives
`Ahat=(Q-1)*(quotient_hat-1)+z+1>=2`. The two native units' removed fields
are sums and products of retained positive data, with
`F3=16*Ahat-8>=24` in the packed AND index. Thus restoration of all fifteen
fields is positive even on child tuples which fail the retained equations.
No divisibility, native power, or canonical-witness assumption is needed
for this graph restoration.

The [joint affine rewrite](u15_packed_joint_affine586.md) then removes
another **25 additions** from either interface. Its standalone result on
611 is 586; this compiler applies the same authenticated rewrite to 561.
It leaves the complete polynomial unchanged on every supplied tuple.

For each literal rule `(source,read,target,direction,write)`, partition the
29 positive edge hats by the three Boolean table entries
`(read,direction,write)`. The eight class sums share the arithmetic for
`J,S,Dir,W,WD`. Their offsets remain respectively 29, 14, 15, 17 and 9.
Thirteen useful source-state pair sums and two additional cross pairs also
serve the centered state projections. Their exact values remain

```
Qdev = sum_i (source_i-7)*(edge_i-1),
Ndev = sum_i (target_i-7)*(edge_i-1).
```

The source and target state offsets are still -6 and +17. These are
computed signed expressions, not additional positive witnesses. The complete
seven-projection block changes from 124=12M+112A gates to 99=12M+87A.
The helper pins that entire incoming affine block and proves that no removed
private intermediate has another downstream or metadata consumer. Every
outgoing reference is through one of the seven proved equal cut registers.

The combined arithmetic ledger is therefore:

| Stage | Ordinary polynomial | Raw polynomial | Ordinary witnesses / comparisons |
|---|---:|---:|---:|
| Centered parent | 611 | 368 | 102 / 46 |
| Power reuse and tape normalization | 606 | 363 | 102 / 46 |
| Fifteen positive loader definitions | 561 | 363 | 87 / 31 |
| Joint affine sharing | **536** | **338** | **87 / 31** |

These are explicit complete schedules, not an optimality claim for either
the affine block or the whole compiler.

## Complete polynomial and zero-set correspondences

Write `F536`, `F561`, and `F611` for the actual emitted polynomials.
The first two have exactly the same coordinate interface. Their seven
affine cut vectors agree coefficient by coefficient, including constant
offsets. The compiler independently reconstructs each as a 30-entry integer
vector in the 29 hats and the constant 1, then checks all retained expression
DAGs, all comparison residuals, all semantic/tag/loader registers, and the
complete finalizer. Consequently

```
F536(v) = F561(v)
```

is an identity over the integers and hence over the rationals or reals.
It does not assume one-hotness, native AND, a valid history, or a zero.

Let `R(v)` restore the fifteen original 611 loader coordinates, and let
`tL,tR` be the two normalized tape residuals. The already reviewed graph
identity composes to give

```
F611(R(v)) = F536(v) + 3*(tL(v)^2+tR(v)^2).
```

The deleted defining residuals vanish identically on this graph. Every other
parent residual is unchanged, except that each old tape residual is twice
its child residual. Since all complete polynomials are sums of squares,
their zeros correspond in both directions. On any parent zero, the deleted
defining equations force precisely `R`; forgetting the fifteen coordinates
and restoring recovers that full parent tuple. Together with the unconditional
integer positivity proof above, this is a bijection of the **complete positive
zero sets**, preserving the ordinary input and all retained witnesses.
In the raw interface the coordinate map is the identity.

These two statements must remain distinct: 536 and 561 have the same
polynomial on the same coordinates; comparison with 611 uses the restoration
graph and the displayed nonzero correction away from its zeros.

The inherited theorem therefore retains the full unbounded first-halt
relation on the same effective valid-program slices. The positive ordinary
input, four fixed positive program numerals, input loader, synchronization,
typing and acceptance costs are all included. Arbitrary positive program
tuples are not asserted to encode valid programs. There is no external
time horizon and no uncounted history decoder in this construction.

## Exact degree

The downstream compiler recomputes degree after eliminating its coordinates.
Every loader residual has degree at most 726, while the retained history
native residual attains degree 968. The whole SOS has upper degree 1936.
Its nonzero top coefficient is certified modulo two primes, and conservative
dependency tracking proves that coefficient independent of the fixed program
numerals. This proves exact degree 1936 for every fixed valid program slice.

The full polynomial identity `F536=F561` transfers that exact degree without
any new assumption about positivity or zeros. The 536 constructor also
independently propagates its own source degree bound. Its ledger deliberately
retains the parent's conservative `exact_degree_claimed=False`; the attached
source and leading-coefficient certificates state the proved result.

## Public interfaces and authenticated provenance

The maintained compiler pins both the downstream source and the narrow
affine-rewrite helper. Its private cache contains the canonical packets;
public access rechecks those sources and the inherited lineage. Every public
packet/source accessor returns a copy. Exact Boolean switches, complete
coordinate sets, exact integer scalars, and complete type-sensitive packet
matching prevent Boolean/float aliases or modified metadata from being
accepted as canonical objects.

The two ancestors are explicit:

- `canonical_parent()` returns the immediate 561 arithmetic parent, with
  the same coordinates and the same polynomial.
- `graph_ancestor()` returns 611. `restore_ancestor_assignment()` and
  `project_ancestor_assignment()` implement its graph correspondence.
- `identity()` checks the full polynomial and residual equality to 561.
  `ancestor_identity()` checks the composed corrected SOS identity to 611.

`build`, `checked`, `polynomial_source`, and `evaluate` expose the complete
compiler. Default assignments use natural `L0,R0` in the raw interface and
strictly positive values for all other supplied coordinates. `signed=True`
allows exact integer algebraic evaluation. Projection defaults to
`require_graph=True`; opting out only forgets coordinates and does not assert
that an arbitrary ancestor tuple lies on the graph.

The immediate-parent descriptor names 561. The original comparison map is
renamed `ancestor_comparison_map`, with current child operands checked
against the new source; it is not presented as a map to the immediate parent.
All computed-loader register aliases and the affine-rewrite provenance are
retained and checked.

## Replay and evidence

From the maintained directory:

```sh
python u15_packed_joint_affine536.py
```

An isolated copy may specify `--root /path/to/native-stream-queue`.
The default compares the full saved JSON with exact types; `--write`
explicitly regenerates it. Assertions remain enabled, as required by the
authenticated research compiler family.

The author replay checks 192 complete parent/ancestor identities, including
96 signed assignments and 4,032 individual retained residual identities;
all graph roundtrips pass. It rejects 1,227 malformed calls and checks eight
defensive-copy boundaries. Exact affine-vector and complete downstream-DAG
certificates cover both interfaces. These finite evaluations corroborate the
all-value proof; they do not materialize astronomical Pell witnesses or
search the unbounded positive solution set.


The [independent review](review_u15_joint536.md),
[checker](review_u15_joint536.py), and [receipt](review_u15_joint536.json)
verify 14 exact affine matrices, both complete residual/SOS DAG identities,
four independent nonzero leading-coefficient certificates, and 64 complete
parent/ancestor evaluations with 1,344 residual comparisons. They also check
158 malformed calls, six defensive-copy boundaries, 15 explicit off-graph
projection cases, and three source-pin rejections after warm caches. The
review's positivity theorem is the separately reviewed 561 graph proof;
it does not infer positivity from numerical sampling. A second proofread
checked the inherited graph, domain and degree statements in this note.
