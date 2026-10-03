# Six-unit partition frontier: 106/42, 108/28 and 110/24

The complete [source](complete_six_unit_partition_frontier106.py) and [receipt](complete_six_unit_partition_frontier106.json) emit **151 distinct paid polynomials** on the same 24 positive witnesses as the retained-a,c asymmetric parent. All preserve its positive integer zero tuples. A marked subset of **77** also has a proof preserving its entire integer zero set. The additional 74 use a first-norm sign lemma on the positive domain; no unrestricted integer-zero equivalence is asserted for them.

The default has **106 operations, exact degree 42, nine equations and 24 positive witnesses**, with ledger `53M+53A`. The positive-domain family frontier is `(106,42), (108,28), (110,24)`. The stronger integer-certified subset has frontier `(108,30), (110,24)`. These are full ordinary-input universal tradeoffs inherited from the parent on its admissible fixed-program slices. The separate 86-operation minimum-count result remains unchanged.

This maintained packet follows the [bounded six-unit scout](complete_bound_unit_scout.md) and the [37-partition five-unit packet](complete_unit_partition_frontier109.md). It saves all 151 sources and their proofs once; the 77 stronger cases are annotations of those same sources, not a second set of emitted circuits.

## Exact source change and complete interface

The actual starting polynomial is the 113-operation, 13-equation asymmetric `sos` form of [complete113_asymmetric_retained109](complete113_asymmetric_retained109.md). It has 24 supplied positive witnesses, ordinary input x and six compiled numeral ports. Its parent proof, raw source, ordinary strong equation, input norm, scale conditions and input-encoding obligations are preserved. There is no new witness, coordinate map, external horizon or weaker native kernel.

The already paid five units are, in order,

```
N0 = g^2 + L(2g-k),                 L=X*Y^2*k,
Nm = d_main^2 - Delta*c^2,
Ni = mu^2 - Delta*kappa^2,
Na = (i*c^2)^2*((j*c-r)^2-y_aux^2) + y_aux^2,
Nk = k-r-hE,
```

where `g=tau_gap`, `Delta=a^2+4a+3`, `E=XY`, `k=eta+zeta`, `X=wq` and `Y=sq^3`. The roots `d_main,mu,kappa` are the existing computed ports, not additional supplied coordinates. The five-unit core and private comparison-side transformations are exactly those reviewed in the preceding packet.

The sixth unit is index 5 in the packet's unit order:

```
Nb = raw_bound-repunit,
raw_bound = Z+W+alpha+twice_cell_bits*x,
repunit = Bm1*Jrep,
q = repunit+1.
```

The old comparison is `raw_bound=q`. Thus `Nb-1=raw_bound-q` as an all-value polynomial identity. Computing Nb costs **one additional subtraction**. The q register has other live consumers and remains in the complete source; it is not declared private or deleted. All its consumers and all other input arithmetic stay paid.

The six unit-related parent residuals are replaced by oriented unit-minus-one residuals; the first orientation is `1-N0`, and the others are `Ni-1`. Squaring removes the first sign. All seven remaining comparison residuals stay exactly unchanged. Every complete packet retains both its current comparison map and the historical original-raw comparison map, with earlier positive-definition deletions still marked historical.

## Two zero-equivalence theorems

On every integer tuple, `Delta` is 0 or 3 modulo 4. Consequently Nm and Ni cannot equal -1. Writing `t=i*c^2` and `U=j*c-r`, the auxiliary unit is `t^2 U^2+(1-t^2)y_aux^2`: modulo 4 it is `y_aux^2` if t is even and `U^2` if t is odd. Hence Na cannot be -1 either. These exclusions do not use any other residual equation.

An integer product equal to one has every factor in `{1,-1}`. Therefore a group with at most one unprotected unit forces all its factors to one. If every block contains at most one of `{N0,Nk,Nb}`, its product equations are equivalent to all six original unit equations over the **entire integer domain**. Together with the seven unchanged squares, this proves same-coordinate equality of integer zero sets for the 77 marked partitions.

For all 151 partitions we additionally use a positive-domain sign exclusion for N0. The exact lemma already appears in the pinned asymmetric parent's Section 2. Here are its hypotheses and proof in the required order.

Before using any residual, strict positivity gives `q=Bm1*Jrep+1>=2`, and therefore

```
V=X*Y^2=w*s^2*q^7>1,
k=eta+zeta>0,
T=Vk+g>0,
N0=T^2-V(V+1)k^2.
```

For an integer `V>1`, suppose `T^2-Dk^2=-1` with `T,k>0` and `D=V(V+1)`. Choose such a solution with minimal positive k and put `P=2V+1`. Define

```
k'=Pk-2T,
T'=PT-2Dk.
```

Since `P^2-4D=1`, direct expansion preserves the norm. Also

```
P^2*k^2-4*T^2=k^2+4>0,
T^2-V^2*k^2=V*k^2-1>0.
```

The first identity gives `k'>0`; the second gives `k'<k`. The preserved norm implies `T'^2=D*k'^2-1>0`. Replacing T' by its nonzero absolute value yields a smaller positive-k solution, a contradiction. The checker proves norm preservation symbolically. This argument precedes the old equations and the parent's universal theorem; it assumes no already-typed computation or restored norm equation.

Thus N0,Nm,Ni,Na are all protected on the positive domain. Each partition separating Nk and Nb has at most one unprotected factor in each block and preserves **positive integer zero tuples**. The same admissible compiled numeral recipe and inherited unbounded ordinary-input theorem apply. The extra 74 partitions do not claim an all-integer theorem, nor a theorem over natural tuples allowing zero, rationals or reals.

The receipt includes an actual integer source assignment with N0=-1: it has `Jrep=0`, `zeta=0` and `g=0`, giving `q=1,V=1,k=1`. This is a boundary example for the sign lemma only. It is not asserted to be a full zero of any new polynomial, and the absence of an all-integer certificate for the extra 74 is not a proof that their actual integer zero sets differ.

## All-value polynomial relation

For any emitted partition G, regardless of its zero-equivalence domain,

```
F_G-F_parent
 = sum_(blocks C in G) (product_(i in C) Ni-1)^2
   - sum_(six units i) (Ni-1)^2.
```

This is an exact complete polynomial identity over every commutative ring. The seven ordinary squares cancel; all six unit residuals are checked against their actual old source expressions, including the new bound and existing index affine identities. A source interner proves every common retained expression and each complete product schedule. The receipt stores the abstract six-unit correction coefficients for every form, along with the entire literal SOS finalizer.

Only the all-singleton partition has full polynomial identity with the parent. For any nonsingleton partition, remove the singleton blocks from its correction. A group containing the remaining highest-degree individual factor has strictly larger degree than that factor, since all six factor degrees are positive. The highest product-square degree thus exceeds every subtracted singleton-square degree. The nonzero SOS of maximal product leaders cannot cancel over the reals, proving that the actual correction is nonzero. This argument uses the exact source leaders below, not an assumption that six independent formal units remain independent after source substitution.

The all-singleton source is polynomially identical but costs one more operation than the literal 113 parent because the added bound subtraction is paid. It is retained in the census for completeness, not advertised as an improvement.

## Literal schedule and complete costs

The six-unit core costs `76=40M+36A`. A partition into k blocks uses `6-k` extra multiplications and has `7+k` comparisons. Its finalizer pays one subtraction and one square per comparison, plus `6+k` accumulator additions. Thus

```
certificate M = 46-k, certificate A = 36,
complete M = 53, complete A = 49+2k,
complete operations = 102+2k.
```

All supplied fields and all source gates are live. Multiplication by fixed numerals, the ordinary loader arithmetic, bound/index ports, every residual and the finalizer are charged. Group multiplication uses increasing unit order and a fixed left-associated schedule; no unrecorded sharing search is involved.

| k | Positive-certified forms | Integer-certified subset | Equations | Certificate gates | Full operations |
|---:|---:|---:|---:|---:|---:|
| 2 | 16 | 0 | 9 | 80 | 106 |
| 3 | 65 | 27 | 10 | 79 | 108 |
| 4 | 55 | 37 | 11 | 78 | 110 |
| 5 | 14 | 12 | 12 | 77 | 112 |
| 6 | 1 | 1 | 13 | 76 | 114 |

The 151 unique full sources total **16,448 gates**, comprising 8,003 multiplications and 8,445 additions. They contain 11,859 certificate gates and 1,580 comparisons. Each source is present in full, including witnesses, fixed ports, complete comparisons, finalizer, ledgers, source proof, correction and exact degree certificate.

## Finite partition census and frontiers

The labels are ordered `(N0,Nm,Ni,Na,Nk,Nb)`. The canonical insertion recursion enumerates all `Bell(6)=203` set partitions exactly once. The 151 positive-certified partitions separate Nk from Nb: contracting that pair counts the excluded `Bell(5)=52`. This is a restricted family, and the other 52 partitions are not classified as unsound.

For the stronger family the three labels N0,Nk,Nb must be in different blocks. Inclusion-exclusion gives

```
Bell(6)-3*Bell(5)+2*Bell(4)=203-156+30=77.
```

The per-block counts in the table are checked against the complete emitted sources. Every one of these 77 is among the 151; no duplicate packet is emitted.

Representative complete frontier forms are:

| Domain certified | Group equations | Full ledger | Exact degree |
|---|---|---:|---:|
| Positive | `N0*Ni*Nb=1`, `Nm*Na*Nk=1` | `106=53M+53A` | 42 |
| Positive | `N0*Nb=1`, `Nm*Na=1`, `Ni*Nk=1` | `108=53M+55A` | 28 |
| Integer | `N0=1`, `Nm*Na*Nb=1`, `Ni*Nk=1` | `108=53M+55A` | 30 |
| Integer | `N0=1`, `Nm*Nk=1`, `Ni*Nb=1`, `Na=1` | `110=53M+57A` | 24 |

The family frontiers are therefore positive `(106,42),(108,28),(110,24)` and integer-certified `(108,30),(110,24)`. Within the positive family, the first two frontier partitions are unique and the last has four attaining partitions, all saved. These claims concern the explicit source schedule and sign-certified partition families, not global arithmetic optimality or all possible regroupings.

The weights below sum to 41. Two blocks require maximum weight at least 21; three require at least 14; the weight-12 first unit gives the lower bound 12 for four or more. The displayed positive schedules attain these lower bounds. In the stronger three-block family a weight-at-most-14 first block must contain N0 alone, since Nk and Nb cannot join it and the lightest protected unit has weight 4. The remaining weight 29 cannot fit in two blocks of capacity 14. Weight 15 is attained, giving the exact stronger degree-30 minimum. These short bounds agree with the exhaustive actual-source census.

Combined with the preceding 37-family catalogue, the new positive frontier replaces `107/42,109/28,111/24` by `106/42,108/28,110/24`. The earlier points through `98/44` and the independent minimum-count bound 86 are unchanged. Stronger-domain labels are preserved even where a positive-only point dominates them arithmetically.

## Exact degrees, including bound-leader specialization

Degree assigns weight one to the ordinary input and supplied witnesses and zero to the six fixed compiled numeral ports. Put `b=Bm1`, `J=Jrep` and

```
Dtop=b*w*J+4*ga*a,
Mtop=Dtop^2+2*a*c*Dtop.
```

Exact multivariate expansion of the complete 76-gate core gives:

| Unit | Degree | Highest homogeneous part |
|---|---:|---|
| N0 | 12 | `b^7*w*s^2*(eta+zeta)*J^7*(2g-eta-zeta)` |
| Nm | 4 | `Mtop` |
| Ni | 7 | `-4*delta^2*a^5` |
| Na | 10 | `i^2*j^2*c^6` |
| Nk | 7 | `-h*w*s*b^4*J^4` |
| Nb | 1 | `Z+W+alpha+twice_cell_bits*x-b*J` |

The seven other residuals have exact degrees `[3,4,5,6,6,2,3]`. The actual norm cancellations are included in this expansion. Products have the sum of their unit degrees, and the complete top degree is twice the largest block weight. All maximal residual squares are included when degrees tie.

The bound leader has alpha coefficient one, so no choice of fixed numerals can make it the zero polynomial. The uniform certificate does not set all variables to one and hope that this affine form is nonzero. Only Nb contains alpha. If its block is among the maximal-degree blocks, the checker extracts the alpha-squared coefficient of the complete highest SOS; it is the square of that block's other unit leaders, with no contribution from another block. If the bound block is not maximal, the complete leader is alpha-free. After that extraction, set `g=2` and the other variable coordinates to one, leaving b formal. In every form the resulting polynomial in b is nonzero with positive coefficients. It is independent of `twice_cell_bits` and the other fixed numerals, and is positive for every admissible `b>0`. This proves exact degree uniformly, not merely on sampled compiler constants.

For the representative sources, writing `Ftop,Itop,Atop,Ktop,Btop` for the corresponding table entries, the highest polynomials are

```
106/42: (Ktop*Mtop*Atop)^2,
108/28: (Mtop*Atop)^2+(Ktop*Itop)^2,
108/30: (Btop*Mtop*Atop)^2,
110/24 displayed above: Ftop^2.
```

Other degree-24 attaining partitions may have tied maximal residuals; their complete leaders are saved separately. The degree-28 form has two maximal residuals, and coefficient `ga^4*a^4*i^4*j^4*c^12 = 256` in their squared sum. Every finalizer is analyzed with its actual maximal set rather than an inherited unique-leader assertion.

## Contracts, provenance and replay

`build(partition=None,root=...)` defaults to `[[0,2,5],[1,3,4]]`, the positive 106/42 form. Explicit partitions are canonical lists of increasing integer-index lists covering 0 through 5 exactly once, ordered by first index, and must separate indices 4 and 5. `rewrite` accepts only the complete authenticated asymmetric `sos` parent. `checked`, `polynomial_source`, `evaluate` and `degree_certificate` rebuild and compare the entire canonical packet using exact types.

Each packet has `positive_zero_equivalent=True`. The field `integer_zero_equivalence_certified` is true on exactly 77 packets; false means that stronger theorem is **not certified**, rather than disproved. `zero_theorem_domain` and `first_norm_descent_used` make this distinction explicit. `full_polynomial_identity` is true only for the all-singleton form. No mutable packet cache is exposed. Evaluation requires the full exact integer assignment, strictly positive by default. `signed=True` is available for polynomial evaluation on every packet; it does not broaden the packet's semantic theorem domain.

Every construction checks 31 parent, source, receipt and proof pins. A present mismatched proof file is rejected; it cannot be bypassed using a valid fallback. The source reads pinned JSON packets and does not execute historical modules. The frozen scout's complete core and all 151 census records are additionally cross-checked as **provenance consistency**, not advertised as independent evidence for this maintained implementation.

The receipt records 604 complete source corrections, including 302 signed-integer and 151 rational cases; 7,852 parent residual checks; 133,056 finite integer-factor cases; 195,696 finite positive-sign factor cases; 128 modular cases; 174 rejected malformed calls; six copy checks; 31 warmed pin rejections; and all three actual relative proof mismatches rejected despite a valid fallback. The general sign, source and degree proofs above establish the unbounded claims; the finite tests supplement them. No astronomical accepting Pell witness is materialized.

```
python complete_six_unit_partition_frontier106.py \
  --root /path/to/native-stream-queue \
  --output /tmp/six-unit-frontier.json \
  --expect complete_six_unit_partition_frontier106.json
```

The replay uses only the standard library. No historical whole suite is run, and the original parent artifacts are not changed.
