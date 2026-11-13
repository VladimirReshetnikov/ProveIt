# Unscale the first residual: 14 inputs, 80 operations, degree 60

This candidate is a **pointwise positive-integer same-zero form** of the independently reviewed 14-input 84/60 q-cube graph. It has **80 live binary operations and exact specialized degree 60** at the authenticated compact44 ports. The argument and checks are submitted for independent review. The local zero-set equivalence requires `beta>0`, but no decoder or coordinate change; the upstream comparison with a consistency equation retains the 84 graph's external compact44 decoder, source/provider and file-binding qualifications. No new Lean/iPRA theorem, PDF interpretation, or global minimality claim is made.

## Exact unscaling

Both graphs use the same 14 inputs and four fixed ports. In the 84 graph write

```
b=J*beta, q=b+1, M=q³*b,
g31=ell+k−r,  g41=1+ell*(ell+k),
Z=M*g31,     A0_old=Z²−M²*g41.
```

The candidate replaces the first residual by

```
A0_new=g31²−g41,       A0_old=M²*A0_new.
```

All other four residuals are literally unchanged. If beta and the inputs are strictly positive, then `M>0`, so `A0_old=0` if and only if `A0_new=0`. Each output is a sum of five integer squares; hence it vanishes exactly when its five residuals vanish. The graphs therefore have the same zero set **at each positive valuation**, with no change of witnesses and no use of the 84 graph's decoder or old-gamma positivity. This does not claim pointwise equivalence when `M=0`, nor equality of the output polynomials. In fact `Pold−Pnew=(M⁴−1)*A0_new²` exactly.

## Literal graph and degree

The checker pins the parent, verifies that M occurs only in Z and `M²`, and reconstructs the exact row delta: delete the M, Z, `M²` and `M²*g41` gates, square g31 directly, and subtract g41. All 80 gates, 14 inputs and all four fixed leaves remain live. There are 42 multiplications, 21 additions and 17 subtractions. The checker verifies the `M²` residual identity in a free integer-polynomial ring and exercises the full output identity on signed integer controls.

For degree, `deg(ell)≤11` and `deg(k−r)≤1`. With `delta=k−r`, exact cancellation gives

```
A0_new=2*ell*delta+delta²−1−ell*k,
```

so `deg(A0_new)≤12`. The main, auxiliary, strong and guard residual bounds from the reviewed 84 graph remain 30, 23, 22 and 3. Thus the sum of squares has degree at most 60. A full-graph ray with every input t and the authenticated actual port bytes modulo 1,000,000,007 has degree 60 and nonzero leader **979167194**, proving exact specialized integer degree 60 externally.

The checker reauthenticates the P72/P115 payloads and reruns the independent 84 review; it does not replace the unbounded zero argument or compile Lean. Reproduce from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary14-unscale-first80/check.py > /tmp/ordinary14-unscale-first80.json
cmp /tmp/ordinary14-unscale-first80.json research/ordinary14-unscale-first80/result.json
```

Independent external review is recorded in
`../../reviews/ordinary14-unscale-first80-root-independent/`.
