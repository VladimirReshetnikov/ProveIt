# A partial assignment inside both Pell growth bounds

Both necessary growth inequalities in `../current14-carrier64-growth-window/`
can hold at the actual fixed ports while the candidate has no old positive
scalar representation at the same `q,R`. This is still only a **partial
assignment**: it does not solve the main, strong or auxiliary norms and does
not disprove a reverse map changing `q` or `R`.

Use the independently reviewed scalar choices from
`../current14-carrier64-power-window-partial/`:

```
B=94517, q=beta+1=2^B, J=1, F=C=q-1,
G=1, R=(q²-1)+MC+q*MF,
w=2^(R-B), z=K+w, N=(R-1)/2.
```

The fixed-port computation checks `R` is odd, `R>=27`, and `R>3B`.
Consequently all these scalar coordinates are positive, `Nt=1`, and
`X=wq=2^R`. Now choose the scale

```
s=2^(R*N-3B),  Y=sq³=X^N,
E=XY=X^(N+1),  m=EY=X^R.
```

The checked exponent is nonnegative; these are finite symbolic integers,
not materialized. They satisfy `X<Y` and `R+1<E`. Both reviewed growth
inequalities hold strictly:

```
X^N=Y < 2*(Y+1)*6^N,        2Y < 18^N*Y=(18X)^N.
```

Let `j=(R+1)/2` and let `(x,k)` be the Pell coefficients of
`(2m+1+2sqrt(m(m+1)))^j`. The reviewed congruence induction gives
`x=1 (mod E)` and `k=R+1 (mod E)`, with `x>k>=2`. Hence
`n=(x-k+R)/E>0`, `eta=1`, and `zeta=k-1` make the carrier `tau=x` and
the first norm equal 1.

Here the direct recovered `alpha=2-q<0`. In fact every old positive scalar
representation with the same `q` has gap at least `2q-1`, while this gap is
1; fixed ports then make equal `R` impossible. A reverse argument could
change other coordinates, and the unsolved remaining norms may still exclude
this partial assignment. No full zero, global minimum, Lean proof, native
replay, or PDF binding is claimed.

The read-only checker authenticates the current graph and all four compressed
and raw port payloads and verifies the finite rank and exponent conditions.
It never constructs the huge `w`, `s`, or Pell power. The reused transport
and Pell identities were independently checked in the earlier packet.

```sh
python3 -I -S -B research/current14-carrier64-two-sided-window-partial/check.py > /tmp/carrier64-two-sided.json
cmp /tmp/carrier64-two-sided.json research/current14-carrier64-two-sided-window-partial/result.json
```

The independent external review is in
`../../reviews/current14-carrier64-two-sided-window-partial-independent/`.
