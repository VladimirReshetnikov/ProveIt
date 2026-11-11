# Direct ordinate trace congruence: a cancellation obstruction

A proposed way to avoid the separate main Pell trace `D` is to use the
normalized strong/auxiliary argument's recovered ordinate
`c=psi_(a+2)(R)` directly. Put

```
a=Y*(X+1),  H=4*a+3,  c=psi_(a+2)(R),  P=2^R.
```

Because H is odd, 2 is a unit modulo H, and `a+2=5/4 mod H`. The Pell
recurrence therefore gives

```
3*c = 2*(P − P^(-1)) mod H.
```

This identity requires no inverse of 3: it follows by recurrence after
multiplication by 3. Consequently the attractive positive-witness relation

```
3*X*c − 2*(X²−1) = gamma*H
```

is equivalent to `H | (X−P)*(P*X+1)`. It does **not** by itself imply the
power relation `X=P`: the second factor need not be a unit modulo H.

The finite checker verifies the positive local example

```
q=2, X=2, Y=16, R=5, a=48, H=195,
c=psi_50(5)=99,970,001, gamma=3,076,000.
```

It satisfies the proposed relation, `q|X`, `q³|Y`, and `R+1<XY`, but
`X!=2^R=32`; indeed `gcd(2^R*X+1,H)=65`. This is a **local arithmetic
counterexample**, not a zero of the full equation. In particular q=2 is
not a possible current-port value of q, and no first Pell norm, transport
factor, current tuple, internal iPRA derivation, Lean, or PDF binding is
claimed. Additional constraints might still imply the missing cancellation.
The literal direct relation also has no known operation saving.

```
python3 -I -S -B research/current14-trace-congruence-obstruction/check.py > /tmp/trace-congruence.json
cmp /tmp/trace-congruence.json research/current14-trace-congruence-obstruction/result.json
```

Independent external review is recorded in
`../../reviews/current14-trace-congruence-obstruction-independent/`.
