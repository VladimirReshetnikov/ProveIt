# Absorb the q-cubed Y quotient: 14 inputs, 85 operations, degree 56

This equation has **14 strictly positive inputs, 85 live operations and exact
degree 56** at the authenticated compact44 ports. It is a degree/operation
tradeoff with the reviewed 14-input 86/26 residue-guard graph: one fewer
operation and higher degree. Its positive-zero existence is equivalent to
that graph's for any integer ports with `beta>0`. This argument and its finite
graph/degree checks are submitted for independent review; no new Lean/iPRA,
PDF or JSON file-semantics theorem, fresh provider replay or minimum claim is
made.

Let `b=J*beta`, `q=b+1`, `M=q³*b`, `m=X*Y²`, `k=eta+zeta`, and
`ell=m*k`. The 86 graph has first expression

```
Z_old=M*(ell+k−r_old)+Y*b.
```

Replace its positive input Y by a positive input s and set `Y=q³*s` inside
the graph. Replace the first input r_old by a positive input r and use

```
Z_new=M*(ell+k−r).
```

The exact identity `Z_old=Z_new` holds when `r_old=r+s` and `Y=q³*s`.
All other residuals and the transport guard agree at these coordinates. The
checker tests this graph identity at finite arbitrary signed assignments;
the algebra itself is an identity over every commutative ring.

## Both positive-zero maps

A positive 85-graph zero maps immediately to a positive 86 zero by
`Y=q³*s` and `r_old=r+s`. Both are positive and the graph identity preserves
all five residuals.

Conversely take a positive 86 zero. Its first square gives
`Z_old²=M²*(1+ell*(ell+k))`. Since M>0, integer square divisibility gives
`M|Z_old`, and its displayed shape implies `q³|Y`. Write `s=Y/q³>0` and
`tau=|Z_old|/M>0`. Then

```
tau²=1+ell*(ell+k),
(ell+k)²−tau²=ell*k+k²−1>0,
r_old−s=ell+k−Z_old/M=ell+k±tau>0.
```

Thus `r=r_old−s` is a positive integer. With `Y=q³*s`, the exact graph
identity yields a positive 85 zero. No bound on K0 or sign assumption about
the transport expression is needed for these maps. The parent's endpoint,
its fixed-port calibration, and the evidence qualifications for any claimed
consistency relationship are inherited rather than re-proved here.

## Exact gate count and degree

The source adds one gate `Y=q³*s`, deletes the old `Y*b` and final addition
in Z, and renames the prior product as Z: `86+1−2=85`. The checker verifies
the literal graph delta, unique names, topology, liveness of every gate,
all 14 inputs and all four fixed leaves, and the P72/P115 compact44 port
hashes. No new fixed leaf is introduced.

For the degree bound, q has degree 1 and the new Y degree at most 4. Hence

```
deg(U)<=6, deg(a)<=5, deg(c)<=5, deg(H)<=5,
deg(ell)<=10, deg(M)<=4, deg(R)<=4.
```

Writing `Z=M*ell+delta` with `delta=M*(k−r)` gives `deg(delta)<=5`, and

```
A0=2*(M*ell)*delta+delta²−M²*(1+ell*k)
```

has degree at most 19. For the main residual write
`Dstar=U*a*c+Theta`, where `Theta=U*X+H*shift` has degree at most 12. Then

```
A1=2*U*a*c*Theta+Theta²−U²*(1+H*c²)
```

has degree at most 28. The ordinary auxiliary residual has degree at most
21, the strong residual at most 22, and the guard at most 2. The final sum
of squares therefore has degree at most 56. A direct all-inputs-equal ray
with authenticated actual ports has degree 56 and leading coefficient
785330250 modulo 1000000007, proving exact specialized integer degree 56.

The earlier 14-input 65-operation, degree-150 PDF equation has fewer
operations and higher degree; this candidate has not been bound to that PDF
or proved equivalent to its selected consistency sentence inside Lean.
The comparisons concern named equations, not a global optimum.

```
python3 -I -S -B research/ordinary14-qcube85-tradeoff/check.py > /tmp/qcube85.json
cmp /tmp/qcube85.json research/ordinary14-qcube85-tradeoff/result.json
```

The finite checker does not replace the positive-zero proof or the exact
degree upper-bound argument above.

Independent external review is recorded in
`../../reviews/ordinary14-qcube85-tradeoff-independent/`.
