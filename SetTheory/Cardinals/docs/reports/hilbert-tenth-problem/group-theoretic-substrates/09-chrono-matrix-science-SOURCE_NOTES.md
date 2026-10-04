# Literal source and accounting

Date: 4 October 2026. Read this with `ARCHITECTURE.md`. The theorem is on strictly positive ordinary input x and strictly positive integer witnesses. The source uses the actual pinned fixed-context coefficient array. No repository is edited, no upstream program or accepting schedule is executed, and no full article is produced.

## Frozen arithmetic source

`evidence/polynomial-dag.json` is the authoritative fully expanded source. Its only leaves are `input:x`, 41,309 positive witness leaves, and fixed integer literals. All internal gates are binary `+`, `-`, or `*`. The output is exactly the sum of the squares of 23,618 named residuals. All gates, witnesses, and x are live. The 506 ports name existing expressions and do not add operations.

SHA256 pins:

- DAG: `95e2563fcfcaecfdc5918ffd6dd7421896350df8969a38f08cbb5f5060d80034`
- Builder: `722db1e253ac3d241fdb538c46a86ffc15e6c208cb8116d168883b6c5bfaa799`
- Inert upstream countdown receipt: `f365eb9b62242b395b33766d00a246f0ebcd1a28d867cbcf1173037552b916e0`

Every source-generating loop is over a fixed list: 97 branches, four row coordinates, five post streams, fifteen POWER equations, or a fixed emitted node list. No input x, horizon h, offset H, digit size, or witness value controls the source's arity or gate count.

## Exact ledger

| Source region | Multiplications | Additions | Subtractions | Total |
|---|---:|---:|---:|---:|
| Body | 48,475 | 40,494 | 24,194 | 113,163 |
| Residual squares and sum | 23,618 | 23,617 | 23,618 | 70,853 |
| Entire polynomial | 72,093 | 64,111 | 47,812 | 184,016 |

Under the convention that A includes both addition and subtraction, this is `72,093 M + 111,923 A = 184,016` operations. Multiplication by every nontrivial fixed coefficient is charged. Literal constants are free. The builder only omits coefficient multiplications by one and zero summands; it does not make selected matrix arithmetic free.

There are 491 Sub calls: 97 selector masks, 388 branch/row slices, five post-history masks, and one loader-counter mask. Each contains three POWER calls, and two further POWER calls construct H and W. Hence 1,475 POWER, 491 Sub, zero AND, zero SPREAD.

Witness count:

`1475*26 + 491*5 + 504 = 41,309`.

The 504 outer leaves are positive h and ell; two positive H/input gaps; one natural R; 97 natural selectors; 388 natural branch slices; five natural post streams; one natural counter prehistory; four natural endpoint digits; and four positive endpoint gaps. Every mathematical natural is represented as a positive leaf minus one. No zero-valued witness is permitted.

Residual count:

`1475*15 + 491*3 + 20 = 23,618`.

The twenty outer residuals are the H and input bounds (two), repetition (one), selector partition (one), four endpoint bounds, four row chronology equations, one counter chronology equation, two row endpoint equalities, four affine updates, and one countdown update. The tile guards are included in the loader-only counter Sub; terminal n=0 is included in the counter chronology equality.

## Exact degree 12

Syntactic degree propagation gives upper bound twelve. Every residual has degree at most six. The H,D,b expressions have degree one; masks have degree two; each branch scalar coefficient is fixed; chronology has degree two; and offset selector products have degree two. Nested Sub powers are represented by fresh leaf outputs and fifteen defining equations, not by substituting exponential terms into the polynomial.

For any POWER call, the thirteenth residual is

`a^2-1-((w+1)^2-1)(w g)^2`.

Its degree-six homogeneous term is `-w^4 g^2`, where w,g are fresh positive witness leaves. Its square contributes the nonzero degree-twelve term `w^8 g^4`. All highest homogeneous contributions are real polynomial squares, so cannot cancel collectively. Thus the sum-of-squares output has exact degree twelve, not merely an upper bound. The source auditor can additionally verify sparse normalized residual degrees without expanding the entire final polynomial.

This degree is in x and all independent positive witness leaves. It is not the degree of the local upstream polynomial, which remains 194. It is not an assertion about real zeros of the packed certificate; POWER/Sub semantics and digit recovery require integers.

## Complete POWER equations

For base b>=2 and natural exponent e, let `k=e+1,m=b*out`. Introduce positive `out,w,M,g,x,y,u,v,s,t,qb,qv,S`; use positive leaves plus one for `a,beta>=2`; and natural

`dwb,dwk,dyk,alpha1,alpha2,sigma1,sigma2,tau1,tau2,rho1,rho2`.

The fifteen equations are:

1. `x^2=1+(a^2-1)y^2`
2. `u^2=1+(a^2-1)v^2`
3. `s^2=1+(beta^2-1)t^2`
4. `beta=1+4y qb`
5. `beta+u alpha1=a+u alpha2`
6. `v=y^2 qv`
7. `s+u sigma1=x+u sigma2`
8. `t+4y tau1=k+4y tau2`
9. `y=k+dyk`
10. `w=b+dwb`
11. `w=k+dwk`
12. `M=m+S`
13. `a^2=1+((w+1)^2-1)(w g)^2`
14. `2ab=M+(b^2+1)`
15. `x+M rho1=y(a-b)+m+M rho2`

Natural auxiliaries are positive leaves minus one. This contributes exactly 26 positive leaves and 15 residuals. The explicit constructive Pell dependency is stated in `ARCHITECTURE.md`; no new number-theoretic representation is asserted here. The positive auxiliary Pell equation supplies the domain fact a>=b used by the approved specialization, and the strict modulus slack and two-sided congruence quotients are retained.

## Complete Sub equations

For natural mask M and value V use three expanded POWER calls to obtain

`R=2^(M+1)`, `Y=R^V`, `Z=(R+1)^M`.

Natural q,h,r and positive gc,gr satisfy

`Z=(qR+2h+1)Y+r`,
`2h+1+gc=R`,
`r+gr=Y`.

All binomial coefficients of `(R+1)^M` are below R. These strict Euclidean extraction bounds therefore demand an odd coefficient at index V. Its oddness is equivalent to bit containment of V in M. Masks and values zero are included. All five added witnesses and three residuals are counted.

## Domain order and verification scope

All x and witness leaves are positive by the theorem's domain. Positive ell first makes H a power of two at least two. H and x gap clauses give initial-offset and input ranges. D and the fixed positive C make b a power of two greater than D and 97. Positive h makes W=b^h valid; the R equation determines a natural geometric sum. Selector Sub calls precede selector one-hot reasoning; the independent low-block slice proof then bounds U without assuming transition correctness. Post/counter Sub calls and endpoint gaps bound every other digit. Every POWER argument in a Sub is natural, with base at least two, before its semantics are applied. The carry bounds are established from masks and fixed coefficients, before reading the packed affine identities digitwise.

The independent mathematical review in `review/PACKING_REVIEW.md` passes this construction and explicitly distinguishes its semantic scope from a DAG audit. The fresh `check_semantics.py` was inspected and run in isolated Python, importing neither builder nor predecessor code. Its receipt is `evidence/semantic-checks.json`. It passed 1,440 mask probes; all 584 small selector candidates; 960 exact branch partitions; 1,360 arbitrary chronology candidates; 3,104 local tests covering all 97 actual affine branches, wrong outputs, signed extremes, and carry bounds; 120 freshly generated actual-matrix chronological prefixes; and 438 counter candidates, of which six accepted exactly the required phase language. A radix-two counterexample additionally demonstrates why a selector carry bound is substantive.

The fresh prefixes have row magnitudes up to 147 bits and test every packed local, chronology, counter, and input condition; their endpoint equalities are checked against their actual final rows, without claiming that random prefixes accept. The receipt's saved accepting schedules are never read by the checker. These tests do not instantiate astronomically large complete Pell witnesses. Numerical probes support the all-integer proof; they do not replace it. Checker SHA256 is `7de96476edb15521b41c642fa42e887ef156b6862ff52de38a8ca80e5ba0ac57`.

Rebuild is optional for inspection:

`python -I build_certificate.py`

The builder is newly authored and contains the complete macro source. It imports no earlier builder or checker and authenticates the inert receipt before reading its fixed coefficient arrays. The emitted DAG can instead be audited as inert JSON.
