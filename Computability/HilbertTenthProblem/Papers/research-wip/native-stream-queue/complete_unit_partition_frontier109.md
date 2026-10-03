# Five-unit partition frontier: a complete 109-operation polynomial of degree 28

The fully paid [source](complete_unit_partition_frontier109.py) and [receipt](complete_unit_partition_frontier109.json) emit all 37 partitions of the actual five units that separate the first and index units. The new default has **109 operations, exact degree 28, 24 positive witnesses and 11 equations**. Its complete ledger is `53M+56A`. It preserves the entire integer zero set of the frozen asymmetric 113-operation SOS source on exactly the same supplied coordinates.

This finite family has frontier `(107,42), (109,28), (111,24)`, where each pair is complete operation count and exact degree. The new point improves the preceding `(109,32)` point. It is a degree/cost tradeoff, not an improvement to the separate 86-operation minimum-count result. The other 15 set partitions fail this particular protected-factor criterion; this packet does not assert that they are unsound for the actual source or exclude additional sign proofs.

## Actual parent and five unit ports

The starting point is the `sos` form of [complete113_asymmetric_retained109](complete113_asymmetric_retained109.md), with its full 113-operation polynomial, 13 equations and exact degree 24. The [preceding index-unit packet](complete109_index_unit_tradeoffs107.md) established two particular partitions. This successor reuses that exact local arithmetic transformation and emits the entire stated finite family. Twenty-five source, receipt and proof-note byte pins are checked before reading the parent packet; no historical Python modules execute. The three actual `../../1980` proof paths are included and a present mismatched file is always rejected, even when a matching fallback copy exists.

Use the fixed unit order

```
0: N0 = first_unit
1: Nm = main_unit
2: Ni = input_unit
3: Na = aux_unit
4: Nk = index_unit.
```

Write `g=tau_gap`, `k=eta+zeta` as literally computed in the source, `E=XY`, `L=XY^2 k`, and `Delta=(a+2)^2-1`. Then the source ports are

```
N0 = g^2 + L(2g-k),
Nm = d^2 - Delta*c^2,
Ni = mu^2 - Delta*kappa^2,
Na = (i*c^2)^2*((j*c-r)^2-y_aux^2) + y_aux^2,
Nk = k-r-hE.
```

Here `d`, `mu` and `kappa` are the parent's unchanged computed ports `R14`, `exponent_rhs` and `index_rhs`; this notation does not reintroduce supplied witnesses. The source still has `X=wq`, `Y=sq^3` and all eight remaining ordinary residuals, including the ordinary strong equation.

The old first comparison is `1-g^2=L(2g-k)`, whose residual is `1-N0`. The other four selected residuals are `Nm-1`, `Ni-1`, `Na-1` and `Nk-1`. In particular,

```
Nk-1 = (k-r)-hE-1 = k-(r+1+hE).
```

The old `r+1` register feeds only its following `+hE` register, which is private to the index comparison. Replacing these two additions by `(k-r)-hE` preserves their paid cost. Literal consumer checks establish this privacy in the authenticated source. The comparison-private `+1` or `1-...` ports of the four norm equations are similarly converted to actual norm ports without changing the complete 75-gate certificate core. The first norm is not evaluated under a newly assumed off-zero relation: its gap and computed-k expression are the actual parent source.

## Complete integer-zero theorem

For every integer a, `Delta` is 0 or 3 modulo 4. Therefore any integer expression `d^2-Delta*c^2` is not -1 modulo 4. This protects both Nm and Ni. Writing `t=i*c^2` and `U=j*c-r`, the auxiliary norm is

```
Na = t^2*U^2 + (1-t^2)*y_aux^2.
```

If t is even this is `y_aux^2` modulo 4; if t is odd it is `U^2` modulo 4. Thus Na cannot equal -1 on any integer tuple. These facts require neither the strong equation nor positivity. No unconditional sign exclusion is used for N0 or Nk.

For a partition in which 0 and 4 lie in different blocks, each block contains at most one unprotected factor. An integer product equal to one has only factors +1 or -1. Every protected factor must be +1, and the possible remaining factor is then +1 as well. Consequently all block products equal one if and only if all five original units equal one. Singleton blocks are included in this statement.

The emitted polynomial is the sum of squares of the eight unchanged ordinary residuals and one residual `product(block)-1` for each block. Its integer zeros therefore coincide exactly with the parent's integer zeros. The proof applies in both directions on the same coordinates, including signed assignments; the computation/universality interpretation is inherited only on the parent's valid fixed-program, ordinary-input, positive-witness slice. The earlier asymmetric positive-coordinate restoration theorem remains a dependency of that interpretation. No new coordinate map or native/Pell sign hypothesis is being introduced.

Off zero, these are generally different polynomials. The exact complete correction is

```
F_partition-F_parent
 = sum_blocks (product_(i in block) Ni - 1)^2
   - sum_(i=0)^4 (Ni-1)^2.
```

All eight ordinary squares cancel literally, and the first residual's opposite sign disappears on squaring. Every saved form includes the entire coefficient dictionary of this abstract five-unit correction, a literal common-source proof and the complete paid finalizer. The all-singleton form is an exception: its correction is zero and its full polynomial equals the parent polynomial everywhere.

## Exhaustive finite family and complete ledgers

The checker enumerates canonical set partitions by inserting each successive index into an existing block or into a new final block. This visits every partition exactly once. There are `Bell(5)=52` total. Contracting indices 0 and 4 gives a bijection from the partitions that put them together to the `Bell(4)=15` partitions of four elements. Hence precisely 37 partitions meet the criterion.

| Number of blocks k | Partitions | Certificate M | Certificate A | Equations | Complete M | Complete A | Complete operations |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 2 | 8 | 43 | 35 | 10 | 53 | 54 | 107 |
| 3 | 19 | 42 | 35 | 11 | 53 | 56 | 109 |
| 4 | 9 | 41 | 35 | 12 | 53 | 58 | 111 |
| 5 | 1 | 40 | 35 | 13 | 53 | 60 | 113 |

The 75-gate unit core costs `40M+35A`. Forming the block products takes exactly `5-k` multiplications, with no unit reused across groups. Finalizing `8+k` comparisons adds `8+k` subtractions, `8+k` squares and `7+k` accumulator additions. Thus the complete cost is always `53M+(50+2k)A = 103+2k` operations. All supplied fields and gates are live. The saved 37 full sources total 4,039 gates: 1,961 multiplications and 2,078 additions; they contain 2,846 certificate gates and 410 comparisons. There is no omitted input, scale, ratio, strong equation or finalizer cost.

The group products use the canonical increasing unit order and left-associated multiplication, without a search for alternative schedules or sharing. The optimality statement below concerns this explicitly emitted partition family and schedule.

## Exact degrees on fixed-program slices

Let `b=Bm1`, `J=Jrep`, and define homogeneous expressions

```
k = eta+zeta,
Dtop = b*w*J + 4*ga*a,
Mtop = Dtop^2 + 2*a*c*Dtop.
```

Exact expansion of the actual 75-gate core, with the six program-numeral ports assigned degree zero, gives the following highest homogeneous parts:

| Unit | Exact degree | Highest homogeneous part |
|---|---:|---|
| N0 | 12 | `b^7*w*s^2*k*J^7*(2g-k)` |
| Nm | 4 | `Mtop` |
| Ni | 7 | `-4*delta^2*a^5` |
| Na | 10 | `i^2*j^2*c^6` |
| Nk | 7 | `-h*w*s*b^4*J^4` |

The main and input cancellations are computed from the entire source, not from a naive gate-degree upper bound. The other eight residuals have exact degrees `[1,3,4,5,6,6,2,3]`. Multiplying a block multiplies its nonzero unit leaders, so the complete degree is exactly

```
2*max(6, max_blocks sum_(i in block) weight_i),
weights = [12,4,7,10,7].
```

For every form the receipt stores the sum of the squares of **all** maximal residual leaders, not an assumption that the maximal residual is unique. It verifies exact full multivariate coefficient dictionaries for those leaders. Only b among the fixed numeral ports may occur. Setting `g=2` and all other variable coordinates to one yields a nonzero polynomial in b with positive coefficients; hence the asserted degree holds for every admissible `b>0`, independently of the other fixed numerals.

The default partition is

```
[[0], [1,3], [2,4]],
```

namely N0 alone, Nm*Na and Ni*Nk. Its two degree-14 residuals yield the complete degree-28 homogeneous polynomial

```
i^4*j^4*c^12*Mtop^2
 + 16*b^8*h^2*w^2*s^2*J^8*delta^4*a^10.
```

In particular, the coefficient of `ga^4*a^4*i^4*j^4*c^12` is exactly 256, independently of every fixed program numeral. This gives a direct uniform nonvanishing certificate for the new point. Its semantic fixed-program hypotheses remain unchanged even though this one coefficient needs no positivity of b.

## Family frontier and its precise boundary

The four achievable minimum degrees at costs 107,109,111,113 are 42,28,24,24. Hence the last cost is dominated and the family frontier is exactly:

| Operations / degree | Canonical partitions attaining it |
|---|---|
| 107 / 42 | `[[0,2],[1,3,4]]` |
| 109 / 28 | `[[0],[1,3],[2,4]]` |
| 111 / 24 | `[[0],[1,2],[3],[4]]`, `[[0],[1,4],[2],[3]]` |

These multiplicities are checked against all emitted sources. They also follow directly from the five weights: for three blocks, the degree-12 unit must stand alone if the maximum is 14, leaving the unique sums `4+10` and `7+7`. For four blocks, only pairing the weight-4 unit with either weight-7 unit keeps the maximum at 12. The two-block case is independently enumerated and its best split has weights 19 and 21. No claim is made about all arithmetic circuits, other finalizers, coordinate changes or the excluded 15 partitions.

Combined with the recorded earlier frontier, this replaces `(109,32)` by `(109,28)` and leaves the earlier points through `(98,44)`, together with `(107,42)` and `(111,24)`, unchanged. This is an exact paid ordinary universal tradeoff inherited from the parent, not a new universality construction or a newly materialized universal Pell zero.

## API, evidence and replay

`build(partition=None,root=...)` defaults to the new degree-28 form. Explicit partitions are canonical lists of nonempty, increasing integer-index lists, ordered by first index; they must cover indices 0 through 4 exactly once and separate 0 from 4. `rewrite` requires the entire exact canonical parent. `checked`, `polynomial_source`, `evaluate` and `degree_certificate` validate the complete canonical packet and fresh source/proof pins. There is no shared mutable packet cache. Evaluation defaults to exact positive integer coordinates and numeral ports; `signed=True` enables integer polynomial evaluation, not a claim that arbitrary numeral values encode a valid program.

The saved receipt contains all 37 complete sources, source/correction proofs and exact degree certificates, with 296 full numerical corrections (148 signed and 74 rational), 3,848 individual parent-residual checks, 59,200 finite factor/partition cases and 128 modular cases. These samples supplement the all-value source and integer-unit proofs. It also records 382 rejected malformed calls, six independent-copy checks, 25 warmed pin rejections, all three actual relative proof paths rejected even with a valid fallback, and optimized-Python rejection. The finite modular/factor census does not replace the general argument above.

```
python complete_unit_partition_frontier109.py \
  --root /path/to/native-stream-queue \
  --output /tmp/unit-partition-frontier.json \
  --expect complete_unit_partition_frontier109.json
```

Only the standard library is needed. Existing parent files are read and authenticated; no historical author suite is invoked and no parent artifact is changed.
