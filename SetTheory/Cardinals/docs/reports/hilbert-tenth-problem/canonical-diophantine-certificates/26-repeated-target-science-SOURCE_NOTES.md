# Literal source, ledger and fresh evidence

Date: 4 October 2026. Status: complete author-side source/proof packet, with independent component reviews of the recurrence/legality/target lemmas and the exact emitted polynomial source. This is not an article and does not claim an unperformed external full-packet audit.

## 1. Authoritative polynomial

`evidence/polynomial-dag.json` is the literal arithmetic source. Its only leaves are the positive free input `InputPlus`, 3,865 positive witnesses, and fixed integer literals. Every internal gate is binary addition, subtraction or multiplication. Fixed literals are free under the declared counting convention. The output is precisely the sum of the squares of all 2,251 named residuals. All gates, witnesses and the input are live. Forty-four exposed ports identify existing expressions and do not add operations or oracles.

The exact represented relation is valid ordinary base-32 physical 3D periodic-plus-finite-patch input with a finite legal ordinary sequence firing the exactly supplied signed target. Repeated firings are allowed. See `ARCHITECTURE.md` for the full input contract, proof and scope boundaries.

## 2. Exact counts

| Part | Multiplications | Additions | Subtractions | Total |
|---|---:|---:|---:|---:|
| Body | 4,537 | 3,681 | 2,305 | 10,523 |
| Sum of squares | 2,251 | 2,250 | 2,251 | 6,752 |
| Full polynomial | 6,788 | 5,931 | 4,556 | 17,275 |

There are 138 POWER, 34 Sub, eight AND and six SPREAD calls, each fully expanded. Relative to the approved binary-prefix literal source, this particular implementation adds 557 positive witnesses, 328 residuals and 2,497 gates while retaining exact degree 18. These are implementation counts, not minimality claims.

The witness accounting is

`138·26 + 34·5 + 8·3 + 6·4 + 59 = 3865`.

The 59 outer leaves are:

- Eleven physical descriptor/target-code leaves and nine inner Cantor-code leaves
- Five geometric values and three tile bitplanes
- The layer count, radix width, half-radix and radix growth gap
- Three padding multipliers and three interior-mask factors
- One time repetition, three pre/event/final streams and three negative-neighbor quotients
- One selected-legality slack
- Twelve target decode/bound leaves and one target-time natural

The equation accounting is

`138·15 + 34·3 + 8·2 + 6·4 + 39 = 2251`.

The 39 outer clauses are ten Cantor clauses; five geometric equations; tile reconstruction; two radix equations; three box-mask equations; time repetition; recurrence; three neighbor divisions; legality threshold; and twelve signed-target clauses.

POWER uses by role are 102 inside Sub, eighteen direct SPREAD powers, five geometric powers, five physical row/plane/z radices, one patch shift, three box radices, one time-end power, one target spatial point, one target timepoint and one variable-radix base. Their sum is 138.

Every builder loop is over a fixed list: fifteen POWER clauses, ten Cantor positions, three tile bits, three spatial axes, or the already constructed fixed node lists. No physical dimension, horizon, coordinate, witness integer or input value controls the number of generated variables or equations.

## 3. Exact degree 18

Ordinary degree propagation gives an upper bound of eighteen. Independent exact sparse polynomial normalization finds maximum residual degree nine. Exactly these three residuals attain it:

`patch.shift.eq8`, `patch.shift.eq9`, `patch.shift.eq11`.

Their degree-nine homogeneous part is

`−4 p q r d e f tx0 ty0 tz0`,

where `tx0,ty0,tz0` denote the raw strictly positive padding leaves, before the source adds one. Every other residual has degree at most eight. Consequently the degree-eighteen homogeneous part of the final sum of squares is

`48(p q r d e f tx0 ty0 tz0)^2`,

which is nonzero. Hence the exact degree is eighteen. The variable radix adds leaves and masks but no higher-degree residual. The target uses separate POWER calls for `b^index` and `Q^τ`, rather than silently combining the high-degree `Nτ` into the spatial exponent.

## 4. Complete arithmetic macros

### POWER

For natural exponent `e` and base `b≥2`, let `k=e+1`, `m=b·out`. Introduce strictly positive `out,w,M,g,x,y,u,v,s,t,qb,qv,S`, two parameters `a,β≥2`, and natural

`δwb,δwk,δyk,α1,α2,σ1,σ2,τ1,τ2,ρ1,ρ2`.

The fifteen equations are exactly

1. `x²=1+(a²−1)y²`
2. `u²=1+(a²−1)v²`
3. `s²=1+(β²−1)t²`
4. `β=1+4yqb`
5. `β+uα1=a+uα2`
6. `v=y²qv`
7. `s+uσ1=x+uσ2`
8. `t+4yτ1=k+4yτ2`
9. `y=k+δyk`
10. `w=b+δwb`
11. `w=k+δwk`
12. `M=m+S`
13. `a²=1+((w+1)²−1)(wg)²`
14. `2ab=M+(b²+1)`
15. `x+Mρ1=y(a−b)+m+Mρ2`

The natural auxiliaries are positive leaves minus one; `a,β` are positive leaves plus one. These equations contribute twenty-six positive witnesses and fifteen residuals. Their exact semantic theorem is `out=b^e`, in both directions, conditional on the inherited pinned constructive Pell theorem. The positive auxiliary Pell equation implies `a≥b`, as required by the specialization. Strict modulus slack and paired nonnegative congruence quotients are retained.

### Sub

For natural mask `M` and value `V`, three POWER calls give

`R=2^(M+1)`, `Y=R^V`, `Z=(R+1)^M`.

Natural `q,h,r` and positive `gc,gr` satisfy

`Z=(qR+2h+1)Y+r`,
`2h+1+gc=R`,
`r+gr=Y`.

All binomial coefficients in `(R+1)^M` are below `R`, so the strict extraction bounds select the true coefficient at index `V`. That coefficient is odd exactly when every set bit of `V` is a set bit of `M`. Thus this is binary bit containment, including masks and values equal to zero. Five additional witnesses and three outer clauses are counted.

### AND

For natural inputs `X,Y`, introduce natural `Z,a,c`, require

`X=Z+a`, `Y=Z+c`,
`Sub(X,Z)`, `Sub(Y,Z)`, `Sub(a+c,a)`.

The first two Sub clauses permit carry-free removal of the common bits. The last makes the residual supports disjoint, forcing `Z=X AND Y`. Three Sub calls, three natural adapters and two partition clauses are counted.

### SPREAD

For natural `U`, power-of-two base `B≥2`, positive length `n` and stride `s`, a natural stride gap and positive range gap enforce

`s=n+1+gap`, `U+strict=B^n`.

Three explicit POWER calls give

`P=B^n`, `C=B^(s−1)`, `F=C^n`.

Natural copy and mask sums satisfy

`(C−1)G1+1=F`,
`(BC−1)G2+1=FP`.

The result is the expanded AND

`AND(U·G1,(B−1)G2)`.

The stride gap prevents collisions among the copied digit blocks; the diagonal mask selects exactly `Σu_i B^(si)`. All actual bases are powers of two: 32, or powers of `b=32^L`. Four additional witnesses and four outer clauses are counted, as are the AND and its nested Sub/POWER calls. This explicitly pays for both raw-code conversion and physical reshaping.

### Geometric sums

Each of the five geometric calls contains POWER and the scalar equation

`(base−1)value+1=base^length`.

Their denominators are positive. No varying-length sum is a primitive operation in the emitted source.

## 5. Well-founded domains

All six dimensions are positive. Base-32 physical masks have positive lengths and natural inputs. Positive radix width and POWER establish `b≥32`; `2half=b` establishes a positive exact half, and the growth equation establishes `b≥64(K+1)`. Consequently every use of `b−1` or `half−1` is natural.

Conversion and spatial SPREADs explicitly enforce `stride≥length+1`, so their copy exponents are nonnegative and their copy bases exceed one. All other spatial powers have positive bases and nonnegative exponents. The interior-mask and time-stream factors are natural. The time-end base `Q≥2` and exponent `K≥1` meet the POWER contract. Target local coordinates and target time are natural, so neither target power has a signed exponent. All Sub interfaces have natural masks and values before the inherited Sub theorem is applied.

These domain facts concern assignments satisfying the full constraints; individual POWER equations are not being asserted to have the intended semantics on arbitrary invalid assignments. There is no circular use of the count bounds to justify recurrence masks: those masks initially allow arbitrary full digits, and the separate recurrence proof establishes the small counts.

## 6. Fresh evidence and review boundaries

The author-side `check_repeated_semantics.py` is newly authored, inspected and run in isolated Python. It imports no builder, upstream checker, historical schedule, external package or Lean program. It passed:

- 480 explicit base-32-to-variable-radix conversion cases
- All 64 combinations of six dimensions in `{1,2}`, comparing scalar physical reshaping with direct coordinates at 53,056 sites
- 8,840 arbitrary candidate recurrence tableaux, including malicious large digits; 42 valid candidates all had the canonical history
- 700 large-radix pairs checking an intended tableau and an arbitrary competing candidate
- 92,610 local legality/slack cases and 864 multi-slot extreme-slack no-carry cases
- 256 3D space-time boxes, checking exact six-neighbor shifts over 27,440 temporal slots
- All 16,384 three-layer binary-event tableaux for two adjacent initial heights in `0,…,15`; exactly 3,663 were legal
- The admitted `[12,4]` repeated-firing separator and an even-final-count target
- 729 signed-target eleven-field Cantor round trips

The independent `recurrence-review/REVIEW.md` proves the critical recurrence uniqueness and all selected-legality/target bounds, and its own fresh checker passed 334,026 arbitrary recurrence candidates, 37,494 selected-legality cases and 7,814 target-time cases. It includes an undersized-radix counterexample showing why the size condition is substantive. That review does not claim to audit the physical loader or emitted DAG.

The independent `source-review/` checker reconstructs exact sparse formal polynomials from inert JSON. It verifies all 2,251 residuals, all 186 macro interfaces, all 44 ports, the exact witness set, liveness, gate legality/order, the complete sum-of-squares tail, ledger and exact degree. It does not numerically construct the gigantic complete Pell witness for a physical instance. Its separate report states its semantic scope.

Finite probes corroborate formulas and source implementation but do not replace the all-integer proof. This packet's mathematical proof is in `ARCHITECTURE.md`, supplemented by the independent recurrence review and the exact inherited arithmetic theorem. A broader independent full-packet audit can review those interfaces without changing the frozen polynomial.

## 7. Reproduction and frozen source pins

Newly authored builder:

`python -I build_repeated_certificate.py`

Newly authored author-side semantic checks:

`python -I check_repeated_semantics.py`

Independent checkers have their own run instructions in their review directories. Running the builder is unnecessary for auditing: the emitted JSON may be read as inert syntax. No upstream scripts or saved schedules are required.

- DAG SHA256: `7bbc522a7e8ff8af23dd9f4b01b8fa783515b1e1de6941dc9a11e85c92f81ea6`
- Builder SHA256: `c37f455dc5a9a673fb2b980fb5dc41103f9a85e82a97c24cae296ed580fe9928`
- Author semantic checker SHA256: `b7e09f945f7c7cbc1b747f273b274f0b87e833c150c0ab94c0e25a654c32a78d`

`evidence/manifest.json` records final packet hashes and verifies that the earlier binary source/audit files remained unchanged. This packet makes no finite-fold, real-witness, minimality, universal-loader or raw-program compiler claim.
