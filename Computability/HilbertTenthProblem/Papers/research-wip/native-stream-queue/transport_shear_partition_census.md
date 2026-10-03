# The full finite grouping census after the transport shear

The transport quotient change yields **no further operation/degree pair**
within the existing thirteen first-root bases and their thirteen gap-root
counterparts. The [complete census](transport_shear_partition_census.py)
checks **59,262 partitions and 298,672 SOS/anchor choices**. Its
[receipt](transport_shear_partition_census.json) saves all 26 literal cores
and all 202 per-base, per-operation winning complete polynomials.

The resulting finite-family frontier remains

```
86/178,87/134,88/122,89/112,90/108,91/102,92/80,
93/72,94/62,95/54,96/50,97/48,98/44.
```

These upper-bound witnesses were already present in the reviewed
[saved-source transfer](review_transport_shear_frontier_probe.md). The new
result closes the omitted-plan and unsaved-tie questions for this specific
finite grammar. It is not a lower bound for arbitrary arithmetic circuits,
a new universal program construction, or a change to the universal 74/86
operation bounds. The separate 106/42, 108/28 and 110/24 constructions use
a different family and are unaffected.

## Complete family and source construction

The authenticated [first-root grouping source](complete86_first_root_partitions.md)
defines thirteen asymmetric bases: three main variants and five variants
each for the linear-input and auxiliary-gap choices. This packet considers
both its new first-root and old gap-root coordinates, giving 26 bases.
The pinned predecessor's canonical base-building routines reconstruct their
actual source arrays and authenticate all their inherited dependencies.
Its old census and verifier are never called. This explicit reuse is part
of the implementation; the companion independent census uses no parent Python.

Each base receives the literal [transport shear](complete86_transport_quotient_shear.md):
`kinner=Kconstant+wn2` becomes `Kconstant+w`, and the supplied `zplus` becomes
`transport_quotient`. Every other core row stays paid. Its factor list and
ordinary comparison list are retained; only the transport weight changes
from three to two. All 19 witnesses and ordinary positive input remain.
The current helper offers a research CLI, not a newly maintained packet API.

For each base, all partitions of its factor list are enumerated as restricted
growth strings. For each partition, every possible single anchor and the
unanchored SOS are considered, without cost pruning. A fresh emitter writes
all product, subtraction, square, sum and anchor gates for every per-cost
winner. These 202 complete winners contain **19,375 live paid gates**, split
**9,702 multiplications and 9,673 additions/subtractions**. Neither the core
nor the full finalizer is counted from a subset of its live consumers.

If the core has cost `c`, there are `n` factors, `g` groups and `m` retained
ordinary comparisons, the complete cost is

    c+n+3m+2g-1,

except for the sole anchored group with no ordinary comparison, whose
product-minus-one cost is `c+n`. This follows by counting the actual group
products, each residual difference and square, all final sums, and the
anchor's multiplication and two additions. Literal winner emission checks
the formula; independent instruction-class accounting checks it for every
weighted objective. All omitted tied schedules have the same formula.

## Complete identities, positive zeros and exact degrees

The checked literal definitions give `q=r+1`, `X=w*q`, and

    C=q-F-Z-alpha-ell*x,
    Nt_old=(K+w*q)*C+q-F-z*r,
    Nt_new=(K+w)*C+q-F-t*r.

An exact six-atom coefficient expansion proves equality under `z=t+w*C`.
The private-consumer checks connect this local identity to the actual core.
For each of the 202 emitted winners, expression interning then checks every
retained register and the entire unchanged finalizer under this cut. This
includes nonempty anchored finalizers, not only the products and SOS forms
that appeared in the earlier 39 saved sources.

At an integer zero, an SOS forces every displayed residual to vanish. A
single-anchor output has the form

    A*(1+S)-1,

where `S` is a sum of integer squares. Since `1+S` is a positive integer,
zero forces `A=1` and `S=0`. Thus every factor group has product one in both
finalizer modes. Its transport factor is therefore an integer unit.

The already proved noncircular positivity argument applies: for a positive
quotient `v`, `q-F-v*r=1-F-(v-1)*r<=0`. The coefficient of `C` is at least two,
so a unit transport value forces `C>=0`. New zeros restore `z=t+w*C>0`;
old zeros satisfy

    r*t=(K+w+1)*C+Z+alpha+ell*x-epsilon>=2,

for transport sign `epsilon=±1`, giving `t>0`. Each source has a full
positive-zero bijection to its own immediate pre-shear source. The ordinary
input and admissible fixed-program numeral recipe transfer unchanged.
This does not assert identical witness sets across different bases or
positive maps off zero.

All fixed numeral ports have degree zero. The unchanged factor
leaders and retained comparison leaders are inherited from the pinned
parent proofs. The new transport leader is

    T2=w*((B-1)*J-F-Z-alpha-ell*x)-t*(B-1)*J.

It is nonzero uniformly, for example by its `w*F` coefficient `-1`.
Consequently group-product degrees add. If their degrees are `d_j` and
retained ordinary residuals have maximum degree `r0`, the exact degrees are

    SOS:       2*max(r0,d_1,...,d_g),
    anchor a:  d_a+2*max(r0,{d_j:j!=a}).

The product of nonzero real polynomials is nonzero, and the highest parts
of real squares cannot cancel. These facts prove exactness uniformly for
every admissible fixed compiler slice, including ties among maximal groups.
The pure product-minus-one case has no squared residuals and degree `d_a`.
No degree is inferred by imposing a retained equation on an off-zero tuple.

Supplemental checks expand all 190 factor instances across the 26 cores,
then every one of the 202 complete winner polynomials on a modular affine
line. The actual full coefficients attain the stated degrees and the
predicted product/SOS leading coefficients. There are also 808 full scalar
pullbacks, including 202 rational cases, and 18,567 retained-register
identities. These checks supplement the uniform leading-form argument;
no full accepting native Pell tuple is materialized.

## Independent enumeration and subset dynamic programming

The [independent weighted census](transport_shear_weighted_census_independent.md)
reads saved ancestor JSON directly, reconstructs the required gap-core
ancestor sets, and derives the first-root cost change from its actual
private six-gate norm. It executes no parent Python and emits no complete
child source. This scope is distinct from the 202 full-source constructions
above.

Its enumeration selects the entire block containing the least remaining
factor, rather than using the author's restricted growth traversal. It
checks the group-count distribution by the Stirling recurrence. Each
thirteen-base family has six eight-factor, five seven-factor and two
six-factor cores, hence 29,631 partitions and 149,336 finalizer choices.

A second independent method computes the minimum possible maximal group
weight by subset dynamic programming, and scans a distinguished subset
for the anchored cases. All 26 per-base checks agree with the independent
enumerator. Their 202 predicted per-cost minima, M/A counts, complete cost
sum and Pareto set agree with this packet's literal winning sources.
Different tied partitions need not be the same representative.

The independent result is a weighted/core-count audit, not a claim that it
independently reconstructed all 202 final polynomials. The two artifacts
state those scopes separately. Together they resolve the earlier missing
metadata without treating the old 101 winner-ledger records as full sources.

## Reproduction

Only the Python standard library is required:

```sh
python transport_shear_partition_census.py --root WIP \
  --expect transport_shear_partition_census.json
python transport_shear_weighted_census_independent.py --root WIP \
  --expect transport_shear_weighted_census_independent.json
```

Both receipts record their own source hashes and exact pinned dependency
manifests. The source receipt uses a recursive type-sensitive replay; the
independent receipt requires its exact deterministic serialization. Use
`--output FILE` to regenerate either receipt. Both fresh installed replays
pass from a different working directory. Frozen predecessor files remain
unchanged; no broad public API or unrestricted optimality claim is made.
