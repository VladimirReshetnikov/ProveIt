# A four-residual 88-operation, degree-30 free-J graph

The [candidate](candidate.json) has 13 positive inputs, the same four compact44
integer ports, **88 live binary operations** and exact specialized degree
**30**. It has the same zero set at **every integer valuation**, including
arbitrary integer ports, as the reviewed
[88/46 free-J graph](../ordinary13-ordinary-pair88-46/README.md), and hence
as that graph's 87/51 free-J parent. The graph and degree certificates here
are external; the inherited free-J endpoint has an author-side record, not
a paired replay. This is not a new Lean theorem, internal JSON/PDF binding,
proof of consistency, or global minimality claim.

## Exact zero equivalence

The 88/46 graph has finalizer

```
A0² + A1² + (Fa*Fs−1)²,
Fs = 1 + g72.
```

Replace it by

```
A0² + A1² + (Fa−1)² + g72².
```

If the old sum is zero over the integers, its three squares vanish. In
particular `Fa*Fs=1`; both integer factors are units and the reviewed global
mod-4 exclusions show neither can be −1. Hence `Fa=Fs=1` and the new sum
vanishes. Conversely, a zero of the new sum has all four residuals zero, so
`Fa=1`, `g72=0`, `Fs=1`, and the old sum is zero. This proof uses no
positivity or fixed-port hypothesis; finite residue controls in the checker
supplement the unbounded argument.

The candidate deletes the old `Fs=1+g72` gate and the seven-gate old
finalizer, then adds the eight-gate four-square finalizer. Thus it has the
same 88 live gates, with 48 multiplications, 23 additions and 17 subtractions.
All 13 inputs and four fixed leaves are live, and there is no new witness or
fixed leaf.

## Exact degree

Naive syntactic propagation gives degree at most 32, but the leading term of
the first residual cancels. From the pinned source write

```
delta = M*(k+r−k*Bt) + Y*qm−q3*Bt,
Z=M*ell+delta,
A0=Z²−M²*(1+ell*(ell+k)).
```

The checker verifies by exact sparse polynomial arithmetic that

```
A0=2*(M*ell)*delta + delta² − M²*(1+ell*k).
```

The source degrees give `deg(M*ell)<=8`, `deg(delta)<=7`, so
`deg(A0)<=15`. The other residual degrees are at most 14, 13 and 10,
respectively. Hence the complete four-square graph has degree at most 30.
Evaluation of the entire graph with all 13 inputs equal to t and the
authenticated actual compact44 bytes modulo 1,000,000,007 gives degree 30
with leading coefficient **879506020**, proving exact degree 30 over the
specialized integers. This is not a Lean `totalDegree` theorem.

## Comparison and proof boundary

This point improves the reviewed 88/46 free-J graph at the same gate and
variable count, and has one more gate but lower degree than its 87/51
parent. It also improves the numerical operation/degree metrics of the named
P73 91/30 and 92/30 graphs and the P72 93/34 graph. P73's first coordinate
is `3j+1`, while this graph has free J: these are metrics of distinct
encodings, not a same-valuation identity between them. The P72 98/28 and
101/24 records trade more operations for lower degree. Other lower-operation,
higher-degree 13-positive records also remain incomparable. These comparisons
do not claim a global frontier.

The zero equivalence above is mathematical over standard integers. The
parent's all-model/iPRA route and package/provider ancestry are inherited
exactly as described in the 88/46 packet; no new all-model bridge or paired
Lean replay is claimed. JSON/byte correspondence is externally checked,
not a theorem about file or PDF interpretation.

```
python3 -I -S -B research/ordinary13-four-square88-30/check.py > /tmp/four-square88-30.json
cmp /tmp/four-square88-30.json research/ordinary13-four-square88-30/result.json
```

Independent external review is recorded in
`../../reviews/ordinary13-four-square88-30-independent/`; it uses a distinct
weighted full-graph ray with degree 30 and leader 592789705 modulo 1,000,000,007.
