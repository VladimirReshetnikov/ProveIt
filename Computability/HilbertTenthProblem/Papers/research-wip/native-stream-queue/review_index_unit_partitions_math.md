# Independent five-unit grouping theorem and degree-28 audit

**PASS.** The actual frozen index-unit source supports the partition

```
[N0], [Nm,Na], [Ni,Nk]
```

with **109=53M+56A complete operations, 11 comparisons, the same 24 positive witnesses, and exact degree 28**. It has the same entire integer zero set as the asymmetric 113/24 parent. The existing positive ordinary-input theorem therefore transfers on exactly the same admissible fixed-program slices. No new input theorem, coordinate change, or weaker bootstrap is used.

Within the explicitly defined 37-partition family below, the operation/degree frontier is `107/42,109/28,111/24`. This is not global arithmetic optimality, nor a classification of every possible zero-equivalent regrouping.

## Actual source and theorem boundary

The independent [checker](review_index_unit_partitions_math.py) reads the full emitted packets in [complete109_index_unit_tradeoffs107](complete109_index_unit_tradeoffs107.md). It authenticates that source, receipt and note, both preceding independent proof notes, and the four underlying raw/relaxed-Pell/half-parameter proof sources before reading arithmetic. No author module, census function or historical suite is executed. The complete pin list is in the [receipt](review_index_unit_partitions_math.json).

The retained scale and unit definitions are literally

```
q=Bm1*Jrep+1, X=w*q, Y=s*q^3, E=X*Y, k=eta+zeta,
Delta=a^2+4a+3,
N0=tau_gap^2+XY^2*k*(2*tau_gap-k),
Nm=d_main^2-Delta*c^2,
Ni=mu^2-Delta*kappa^2,
Na=(i*c^2)^2*((j*c-r)^2-y_aux^2)+y_aux^2,
Nk=(k-r)-h*E.
```

Here `d_main`, `mu`, and `kappa` are the already paid registers `R14`, `exponent_rhs`, and `index_rhs`, not additional supplied or free fields. Exact expansion verifies all four norm definitions, the discriminant, the index definition, their five original residual identities, and all eight untouched comparison residuals. The original first residual is `1-N0`; its square equals `(N0-1)^2`. The original index residual equals `Nk-1` identically, without any equation hypothesis.

For every integer `a`, `Delta` is zero or three modulo four. Hence `Nm` and `Ni` cannot equal minus one: modulo four their values are respectively a square, or a sum of two squares. Writing `t=i*c^2`, the auxiliary norm is congruent to `y_aux^2` if `t` is even and to `(j*c-r)^2` if `t` is odd, so it also cannot equal minus one. These sign facts hold on every integer tuple; neither the strong equation nor the history theorem is assumed.

An integer product equal to one forces all its factors to be plus or minus one. Therefore any group with at most one of the two unprotected factors `N0,Nk` forces every factor to be plus one. The converse is immediate. Since the complete polynomial is a sum of squares of integer residuals, replacing the five unit equations by such group products preserves the full integer zero set. This is not asserted over rational or real witnesses, and the polynomials generally differ away from zero.

For the 109/28 partition the complete correction to the asymmetric parent is

```
F109/28-F113/24 = D(Nm,Na)+D(Ni,Nk),
D(u,v)=(uv-1)^2-(u-1)^2-(v-1)^2
      =(u-1)(v-1)(uv+u+v-1).
```

The first-unit square and the eight unchanged squares cancel in this correction. The checker verifies the exact full source polynomial and this correction by coefficient dictionaries. The [asymmetric positive restoration review](review_asymmetric_retained109_math.md) and [index-unit source review](review_complete109_index_unit_tradeoffs107.md) retain their original domain and admissible-program obligations; none is strengthened by this grouping argument.

## Complete paid counts and the finite family

The literal five-unit core is still `75=40M+35A`. It computes every supplied interface and every unit exactly once. A partition with `g` blocks appends `5-g` binary multiplications. There are eight unchanged comparison pairs and `g` new pairs. Their fully charged SOS finalizer uses `8+g` subtractions, `8+g` squares and `7+g` summation additions. Consequently

```
M=53, A=50+2g, total=103+2g.
```

The independent emitter reconstructs and checks closure/liveness of the entire schedule for each of the 37 partitions. No norm port, product, constant subtraction or finalizer gate is free. This check concerns the specified literal source schedule; it does not search alternative arithmetic sharing.

There are `Bell(5)=52` set partitions of the five labelled factors. Joining `N0` and `Nk` into one labelled element gives exactly `Bell(4)=15` partitions in which they occupy the same block. Thus exactly 37 separate them. Their counts by number of blocks are:

| Blocks | Partitions | Complete operations | Smallest exact degree |
|---:|---:|---:|---:|
| 2 | 8 | 107 | 42 |
| 3 | 19 | 109 | 28 |
| 4 | 9 | 111 | 24 |
| 5 | 1 | 113 | 24 |

The five-block baseline is included and is dominated within this family. All three frontier points and all attaining partitions are independently enumerated:

- `107/42`: `[N0,Ni] | [Nm,Na,Nk]`.
- `109/28`: `[N0] | [Nm,Na] | [Ni,Nk]`.
- `111/24`: either `[N0] | [Nm,Ni] | [Na] | [Nk]`, or `[N0] | [Nm,Nk] | [Ni] | [Na]`.

The other 15 partitions are outside this protected-unit criterion. At the level of abstract unit values, setting `N0=Nk=-1` and the other three factors to one defeats a same-block argument. This is **not** a claim that such a sign assignment is realizable by all the actual source equations, or that every excluded actual partition is unsound.

## Exact uniform degrees and the complete 109/28 leader

Assign degree one to the ordinary input and all supplied witnesses, and degree zero to the fixed compiler numerals. Write `b=Bm1`, `J=Jrep`, `g=tau_gap`, and define

```
Ltop=b^7*w*s^2*(eta+zeta)*J^7,
Dtop=b*w*J+4*ga*a,
Mtop=Dtop^2+2*a*c*Dtop.
```

Independent exact expansion of the actual 75-gate core gives these highest homogeneous parts:

| Unit | Degree | Highest part |
|---|---:|---|
| N0 | 12 | `Ltop*(2g-eta-zeta)` |
| Nm | 4 | `Mtop` |
| Ni | 7 | `-4*delta^2*a^5` |
| Na | 10 | `i^2*j^2*c^6` |
| Nk | 7 | `-h*w*s*b^4*J^4` |

The exact ordinary residual degrees are `1,3,4,5,6,6,2,3`. Each unit leader remains a nonzero polynomial for every admissible fixed `b>0`. Product degrees therefore add. In the complete SOS, the sum of squares of the maximal homogeneous forms cannot cancel over the reals. It follows that every partition in this family has exact degree twice its largest block-weight sum for weights `(12,4,7,10,7)`. No residual equation is substituted in calculating these formal degrees.

For 109/28 the three grouped residual degrees are `12,14,14`. There are **two** maximal residuals. The complete highest homogeneous polynomial is exactly

```
i^4*j^4*c^12*Mtop^2
 + 16*b^8*h^2*w^2*s^2*J^8*delta^4*a^10.
```

The actual fully expanded 109-gate polynomial has 11,842 monomials; its highest homogeneous component has 13. Every coefficient agrees with the displayed expression. In particular the monomial

```
ga^4*a^4*i^4*j^4*c^12
```

has coefficient **256**, independent of all fixed numeral values. This alone proves nonvanishing of the degree-28 leader uniformly; it does not require a unique leading residual. The admissible positive-program conditions remain necessary for the inherited computational theorem and for the other partition leaders' stated uniform census.

## Replay scope

The saved check includes all 37 literal schedules and 4,039 live paid gates, all five actual unit residuals and eight retained residuals, 128 modulo-four cases, and 59,200 bounded abstract integer-factor cases. The unrestricted sign theorem is the arithmetic proof above, not an inference from those finite cases. The exact full polynomial and coefficient correction are expanded for the new 109/28 source. For the remaining partitions, exact degrees follow from the independently expanded unit leaders and the product/SOS proof; their entire coefficient expansions are not redundantly materialized.

```sh
python review_index_unit_partitions_math.py --root /path/to/native-stream-queue \
  --output /tmp/index-unit-math-replay.json \
  --expect review_index_unit_partitions_math.json
```

This is a source-based mathematical and finite-census review. It does not audit the forthcoming maintained partition compiler's public API, claim a new canonical input theorem, or materialize an accepting universal Pell witness.
