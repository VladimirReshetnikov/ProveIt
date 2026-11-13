# A free-J conditional sphere with the same 88/30 metrics

The [candidate](candidate.json) is a pointwise positive-integer zero-equivalent alternative to the reviewed free-J 88/30 graph. It has 13 positive inputs, the same four fixed ports, **88 live binary operations and exact specialized degree 30**. This is an equal-metric search form, not an operation or degree improvement. It is submitted for independent review; no Lean theorem, PDF/file-semantics binding, new endpoint replay, or global minimality claim is made.

## Positive-domain equivalence

Keep the parent graph's four residuals, and write

```
I=i*c²,  Q=Delta*(f²−1),  g72=I²−Q,
y=V+u,   Fa=y²−Q*(y²−V²).
```

The old and new outputs are respectively

```
Pold=A0²+A1²+(Fa−1)²+g72²,
Pnew=A0²+A1²+Fa²+g72²−1.
```

For strictly positive inputs, `a=XY+Y≥2`, `Delta=(a+2)²−1≥15`, `c=eta+Y*(eta+zeta)≥3`, `I≥9`, and `u>0`. We show `Fa²+g72²−1≥0`:

* If `f≥2`, then `Q>1`. If `Fa=0`, the equality `(Q−1)*y²=Q*V²` forces y and V both nonzero, because `y−V=u>0`. Since Q and Q−1 are coprime, prime valuations make both positive squares, impossible for consecutive positive integers. Thus `Fa≠0`.
* If `f=1`, then `Q=0` and `Fa=y²`. When `Fa=0`, `g72=I²≥81`, so the strong square is greater than one.

For all integer valuations, `Delta` and `f²−1` are each 0 or 3 modulo 4, so Q is 0 or 1 modulo 4 and Fa is congruent to y² or V². Thus `Fa≠−1`. If `Pnew=0`, its three nonnegative parts `A0²`, `A1²`, and `Fa²+g72²−1` all vanish. The `Fa=0` branch is impossible in the last equality, so `Fa=1` and `g72=0`; the old four squares vanish. Conversely every old zero has `A0=A1=g72=0` and `Fa=1`, hence is a new zero. This is an unbounded arithmetic argument; the checker is not a Lean proof. We do not claim pointwise equivalence on arbitrary signed integer inputs.

The often-tempting stronger assertion `Fa≠0` on every positive input is false: set all inputs except u to 1, compute the positive actual-port rank R, and take `u=R`. Then `c=3`, `V=−R`, `y=0`, `Fa=0`, and `g72=81`. This is a positive input control, not a full graph zero.

## Literal graph and bounded search

The literal graph removes the `Fa−1` gate, squares Fa, and adds a final subtraction by 1. It has 48 multiplications, 23 additions and 17 subtractions, with all gates, 13 inputs and four ports live. The exact polynomial relationship is `Pnew=Pold+2*(Fa−1)`. The parent has degree 30 and `deg(Fa−1)≤13`, so the new graph has degree at most 30; evaluation of the entire graph at all witnesses `t` and authenticated compact44 port bytes modulo 1,000,000,007 gives degree 30 and leading coefficient 879506020, proving exact specialized integer degree 30.

`beam.py` uses the pinned existing structural rewrite engine, a 300-wide beam for ten depths and an intermediate cap of 90 live gates. It found no graph with fewer than 88 gates. Its common-factor control reduces three gates to two; pruning makes this a bounded observation, not an exhaustive search. The separate 88/30 parent exact-target screens are in `../ordinary13-88-local-rewrite-screen/`. Neither screen covers arbitrary positive-domain zero-preserving transformations.

Run from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-freej88-conditional-sphere/check.py > /tmp/freej88-sphere.json
cmp /tmp/freej88-sphere.json research/ordinary13-freej88-conditional-sphere/result.json
python3 -I -S -B research/ordinary13-freej88-conditional-sphere/beam.py > /tmp/freej88-sphere-beam.txt
cmp /tmp/freej88-sphere-beam.txt research/ordinary13-freej88-conditional-sphere/beam-result.txt
```

The finite checker pins the source graph, checks its exact row delta, graph liveness, authenticated bytes and modular ray, and exercises the displayed polynomial relationship on finite controls. The general zero-equivalence proof is the argument above; the upstream free-J endpoint and source/provider qualifications remain those of the reviewed parent.

Independent external review is recorded in
`../../reviews/ordinary13-freej88-conditional-sphere-independent/`.
