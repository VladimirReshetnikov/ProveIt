# A guarded 14-positive-variable, 89-operation, degree-26 graph

This packet proposes a different equation from the 14-variable PDF equation.
It has **14 strictly positive inputs, 89 live arithmetic operations and
exact degree 26** at the authenticated compact44 ports. Its positive-zero
existence is equivalent to that of the independently reviewed 13-input 88/30
free-J parent, under the explicit parameter inequalities below. The proof and
finite graph/degree checks are submitted for independent review. There is no
new Lean or iPRA theorem, JSON/PDF interpretation theorem, fresh replay of
inherited endpoint ancestry, or global minimality claim.

Relative to the signed-fold candidate
`../ordinary13-folded-root86-negated/`, add one positive input `h` and append
three gates

```
guard = Bt−h,   guard2 = guard²,   guarded_out = out+guard2.
```

The signed-fold output is a sum of four integer squares, so the new output
is a sum of five. A positive zero therefore has the four original residuals
zero and `Bt=h>0`. In particular the independently reviewed actual-port
signed-fold zero with negative Bt does not satisfy the guard.

## Positive-zero equivalence

Assume fixed integer ports satisfy

```
beta>0, 0<=K0<(beta+1)².
```

The checker authenticates the actual compact44 ports and checks these
inequalities. For any positive J put `b=J*beta`, `q=b+1`. Then `q>=2`
and `K0<q²`.

**Guarded to parent.** At a positive guarded zero, `Bt=h>0` and all four
signed-fold residuals vanish. The independently reviewed theorem in
`../ordinary13-folded-root86-negated-positive-bt/` constructs a positive
first-root coordinate for the 88/30 parent while keeping the other twelve
parent inputs fixed. That theorem requires only `beta>0`.

**Parent to guarded.** Take any positive 88/30 parent zero. The reviewed
first-norm argument in `../ordinary13-folded-root86-negated-forward/` gives
`Bt>0`, `q³|Y`, `b|Bt`, and a positive integer `tau` satisfying

```
s=Y/q³, t=Bt/b, m=X*Y², k=eta+zeta, ell=m*k,
tau²=1+m*(m+1)*k².
```

Because `C=q−F−alpha<=b−1` and F>0,

```
Bt=C*(X+K0*q)−F*q < b*(X+K0*q),
t < X+K0*q < X+q³ < 2*X*q^6 <= ell.
```

The last two inequalities use `q>=2`, `X>=1`, `Y>=q³`, and `k>=2`.
Keep the other twelve inputs and set the signed-fold input and guard input to

```
sigma=ell+k+s−t+tau > 0,  h=Bt>0.
```

With `M=q³*b`, the signed-fold first expression is `Z=−M*tau`, so its first
residual vanishes. The other three residuals are unchanged from the parent,
and the guard vanishes. This constructs a strictly positive guarded zero.
The two witnesses need not have the same first-root branch; the maps prove
positive-zero **existence** equivalence, not pointwise equality.

## Gate count and degree

The checker reconstructs the candidate as the literal 86-gate signed-fold
source followed by exactly the three displayed gates and verifies that all
89 gates, 14 inputs and four fixed leaves are live. No new fixed leaf is
introduced. The signed-fold output has degree at most 26 by the exact
cancellations in its independently reviewed packet; `Bt` has degree at most
2 and the new guard square has degree at most 4. Thus 26 remains an upper
bound. A direct all-inputs-equal modular ray with the authenticated actual
ports has degree 26 and leading coefficient 316822945 modulo 1000000007,
proving exact degree 26 over the specialized integers.

This trades one more variable and one more operation for degree 26 versus
the 13-positive 88/30 free-J graph. It also trades more operations for lower
degree versus the displayed 14-variable 65/150 PDF equation, but it does not
establish a Lean or PDF correspondence to either source. The parent's source
endpoint and ancestry limitations are inherited rather than resolved here.

## Existing-input guard check

Simply setting `h=F` or `h=alpha` would remove the extra input but makes the
guarded graph have **no** positive zeros under `beta>0`, `K0>=0`. Indeed the
first residual gives `b|Bt`; `Bt>0` implies C>0 and hence
`1<=F,alpha<=b−1`. Consequently neither F nor alpha is a positive multiple
of b. This excludes only those two particular existing-input substitutions;
it does not rule out other guards or 13-input parametrizations.

```
python3 -I -S -B research/ordinary14-guarded-fold89-26/check.py > /tmp/guarded-fold89.json
cmp /tmp/guarded-fold89.json research/ordinary14-guarded-fold89-26/result.json
```

The finite checker does not replace the unbounded arithmetic proof above.

Independent external review is recorded in
`../../reviews/ordinary14-guarded-fold89-26-independent/`.
