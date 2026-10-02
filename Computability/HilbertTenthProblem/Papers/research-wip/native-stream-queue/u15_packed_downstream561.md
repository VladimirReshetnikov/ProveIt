# Complete downstream U15 projection: 561 operations

Reusing powers, dividing two tape equations by their constant factor2, and computing fifteen positive loader fields reduces the complete [611-operation compiler](u15_packed_centered_states611.md) to **561=219M+342A operations**. The raw natural half-tape interface becomes **363=126M+237A**. The complete positive zero sets are in explicit bijection with the parent's: the ordinary interface removes fifteen uniquely defined coordinates, and the raw interface keeps every coordinate.

| Interface | Certificate source | Comparisons | Positive witnesses | Complete polynomial |
|---|---:|---:|---:|---:|
| Natural raw half tapes |331=115M+216A|11|51|363=126M+237A|
| Positive ordinary input, fixed valid program numerals |469=188M+281A|31|87|561=219M+342A|

The source emits every gate and complete sum-of-squares finalizer. Constants and copies are free; each binary addition, subtraction and multiplication, including multiplication by a numerical coefficient, costs one. All emitted gates reach the final output. This improves the direct tape construction; it does not improve the separate87-operation universal polynomial bound. Its87 witnesses are a coordinate count, not that operation bound.

The parent Python pin is `3208cefa385789f2a7774bd348316a99e57f841154c40eed065e159bad4d20ce`. Both actual complete parent descriptors are independently authenticated by type-sensitive structural hashes before rewriting. The child source and receipt are `u15_packed_downstream561.py` and `.json`.

## 1. Four power gates are redundant

The actual parent repunit29 construction already contains P², P³, P⁶, P²⁸. Its packed-region source computes P⁵ using P⁴·P, and its final scale/tag source computes P³⁴ using the chain P⁴→P⁸→P¹⁶→P¹⁷→P³⁴. Use instead

```
P⁵ = P³ P²,
P³⁴ = P²⁸ P⁶.
```

Delete P⁴, P⁸, P¹⁶ and P¹⁷. The replacements preserve the registers named `v254` and `v267`; every downstream semantic value is identical on every integer tuple. The checker independently reconstructs both monomials from actual parent and child rows as univariate polynomials in the actual P register. Exactly four multiplications are saved. No new equation or witness is introduced.

## 2. Two tape residuals have a paid common factor

For the history radix, write D=L0+R0+height and B=64D. The parent compares

```
2(H−L0+P Lf) = B(4H−3ZL+2W−T),
2(G−R0+P Rf) = B(G+3ZR+T−U),
T=2WD+ZU.
```

Here Lf=Lfhat−1, and all letter projections remain the parent's actual paid source. Compute one shared register Bhalf=32D and use

```
H−L0+P Lf = Bhalf(4H−3ZL+2W−T),
G−R0+P Rf = Bhalf(G+3ZR+T−U).
```

Each old residual is exactly twice its new residual, on all integer assignments, without assuming B is a radix or a native equation holds. The two left-side ×2 gates disappear; the shared ×32 gate is added. This saves one multiplication. Every zero is preserved in both directions since the constant2 is nonzero. It changes the off-zero polynomial; no polynomial identity on unchanged assignments is claimed for this stage.

## 3. Fifteen loader fields have positive computed definitions

This stage applies only to the ordinary loader. Distinguish its input radix q and its Q=q³², B_in=2³¹Q from the history B above. All remaining supplied coordinates are positive integers. The outer loader definitions are

```
q = x + input_slack,
J_in = B_in + geometry_index_beta,
P_in = (B_in−1)J_in + 1,
Ahat = (Q−1)(quotient_hat−1) + z + 1.
```

The first three are existing literal defining comparisons, possibly written with the defined coordinate on the right. The fourth is the existing congruence solved for Ahat:

```
Ahat + Q = (Q−1)quotient_hat + z + 2.
```

Its reconstruction uses five gates: Q−1, quotient_hat−1, their product, +z and +1. The old congruence side construction also uses five gates, so this substitution adds no certificate-source cost. On the restoration graph its deleted residual vanishes by the literal identity

```
(Q−1)(quotient_hat−1)+z+1+Q
  = (Q−1)quotient_hat+z+2.
```

The definitions are acyclic in the order q→Q→B_in→J_in→P_in, with Ahat after Q. Their positivity holds **before any native or semantic equation is used**: q≥2, Q≥2³², B_in>1, J_in>0 and P_in>0. Since quotient_hat−1≥0 and z≥1, Ahat≥2. Integrality and the supplied positive-domain lower bound matter; arbitrary positive reals below1 do not satisfy this argument.

The geometry and AND units supply the remaining eleven definitions. For either unit put

```
k = eta+zeta,
s = 2*odd_half+1,
sn2 = s*q_unit,
wn2 = w*q_unit,
UM = wn2*sn2,
a = UM+sn2,
c = k*sn2+eta,
d = wn2+c*a+ga*(4*a+3).
```

Thus k,s,a,c,d are positive from the retained positive coordinates and q_unit>0. For geometry, q_unit=q; for AND, q_unit=16qP_in. The AND unit additionally computes

```
r = F0 + q_unit*(F1 + q_unit*(F2 + q_unit*F3)),
F3 = 16*Ahat−8.
```

F0,F1,F2 remain positive supplied coordinates. The proved Ahat≥2 gives F3>0, hence r>0. Removing geometry's five fields a,c,d,k,s and AND's six a,c,d,k,r,s therefore never introduces a nonpositive restored coordinate, even on a child tuple that fails every retained native equation.

Every source row is retained with these coordinate aliases and topologically reordered, apart from the separately proved power/tape changes and the five-for-five Ahat construction. The source is acyclic; the exact complete descriptor, not a handpicked gadget, is rewritten. The fifteen corresponding defining comparisons are deleted. This removes fifteen witnesses and fifteen finalizer residuals, saving45 operations:15 residual subtractions,15 squares and15 additions to the sum.

## 4. Complete zero-set theorem and exact correction

Let R(v) be the public restoration map, obtained by running the complete child source and inserting the fifteen computed loader coordinates. For the raw form R is the identity. Let F_old be the complete611 parent polynomial and F_new the emitted child polynomial. Let t_L,t_R be the two child tape residuals. The actual-source certificate proves

```
F_old(R(v)) = F_new(v) + 3*(t_L(v)^2+t_R(v)^2)
```

for every integer child tuple, including signed tuples. Fourteen deleted defining rows are exact expression-DAG identities after restoration; the Ahat row uses the displayed affine identity. Every other retained parent residual equals its child residual, except the two tape residuals, which equal twice the corresponding child residuals. Their individual map is exported for every old comparison index. The complete SOS finalizers are literal sums of these squares.

All terms in either SOS are nonnegative over integers. Therefore F_new(v)=0 iff F_old(R(v))=0. Conversely, at any parent zero every deleted defining comparison vanishes. They force exactly the restored values, including Ahat after solving the congruence. Forgetting the fifteen coordinates and restoring is consequently the identity on the complete parent zero set; restoration then forgetting is the identity on every child tuple. These maps give a full integer zero-set bijection. The independent positivity argument in Section3 restricts it to a full positive-zero bijection on the ordinary supplied domain, and the unchanged raw natural/positive mixed domain likewise transfers.

In particular the same ordinary input, fixed valid program slices, unbounded-duration first-halt relation and native witness requirements remain. This does not claim uniqueness of all original native witnesses. The fifteen removed fields themselves have a unique extension. No full Pell witness is materialized by the arithmetic checks.

The operation stages are transparent:

| Stage | Raw complete | Ordinary complete |
|---|---:|---:|
| Frozen parent |368|611|
| Reused P⁵ and P³⁴ powers |364|607|
| Two halved tape residuals |363|606|
| Eleven computed native fields |363|573|
| q,J_in,P_in definitions |363|564|
| Ahat congruence reconstruction |363|561|

The complete polynomial changes and its coordinate set shrinks. Its equality with the parent is asserted only with the explicit correction on the restoration graph.

## 5. Degree and public contracts

Degree is recomputed after substitution; it is not inherited merely from the parent's witness count. Every loader residual has propagated degree at most726, giving SOS degree at most1452. The unchanged history unit still has maximum residual degree968. The full child upper bound is therefore1936 in both forms.

For each complete source, the receipt evaluates the highest homogeneous coefficient along a positive integral direction at both primes1,000,000,007 and1,000,000,009. The results are respectively531489910/846404135 for raw and445469060/435842868 for ordinary, all nonzero. Formal degree propagation specifies the coefficient being evaluated; a nonzero modular value proves it is nonzero over the integers. A parallel dependency-set calculation proves the complete leading coefficient has no fixed-program-parameter dependency. Thus degree1936 is exact on every fixed valid program slice, not only on a selected numerical program instance. The compiler ledger conservatively retains `exact_degree_claimed=False`; the separate checked certificate records this exact-degree result.

Public APIs are `build`, `checked`, `canonical_parent`, `polynomial_source`, `evaluate`, `restore_assignment`, `project_assignment` and `identity`. Every public Boolean switch is exact; assignments require exactly the declared keys and integer types, rejecting floats and Booleans. Default evaluation and restoration enforce the declared positive domain, with natural L0,R0 only in the raw form. `signed=True` is explicit algebraic evaluation, not a positive-domain certification. Projection defaults to `require_graph=True`, rejecting a parent tuple whose deleted fields disagree with restoration. `require_graph=False` only forgets coordinates and promises no off-graph identity.

Canonical packet matching is type-sensitive, including coefficients, containers and metadata. Parent source bytes and the two complete type-tagged descriptors are pinned; inherited source guards are rechecked after a warm cache. Public packet/source accessors return copies; the cache holder is private. A preloaded fake or foreign loader module cannot replace the authenticated consumed source.

## 6. Replay

From the maintained directory:

```sh
python u15_packed_downstream561.py
# Explicit receipt regeneration:
python u15_packed_downstream561.py --write
```

For a standalone scratch copy, pass `--root /path/to/native-stream-queue`. This is a portable sibling/root lookup, with no permanent scratch dependency. SymPy is inherited from the pinned parent's exact state-identity certificate. Assertions must remain enabled for the frozen parent family.

The writer passed128 complete graph-SOS identities,64 signed cases,3,648 individual residual maps,64 positive restorations,1,302 malformed-input rejections, six defensive-copy checks, two cold fake/foreign-loader checks and the private-cache-holder check. These finite cases supplement the all-value source identities and positivity proof. The receipt contains both full emitted packets, complete comparison maps, strict typed parent pins, exact ledgers and degree certificates. Default CLI replay compares the complete saved JSON with exact types. No global optimality or87-operation improvement is claimed.
