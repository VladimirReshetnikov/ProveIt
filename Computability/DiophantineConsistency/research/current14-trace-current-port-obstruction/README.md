# Current-beta local obstruction to direct trace cancellation

This is a symbolic local construction at the **actual current beta port**.
It strengthens `../current14-trace-congruence-obstruction/`: the direct
ordinate congruence can hold with odd `R`, positive `gamma`, `q|X`, `q³|Y`,
and `R+1<XY`, even when `X!=2^R`. It does not satisfy or claim the full
fixed-port rank formula, the first Pell norm, the remaining norm/transport
conditions, or a whole-equation zero. No smaller circuit, Lean theorem,
PDF binding, or consistency conclusion follows.

The pinned actual port is `beta=2^B−1` with odd `B=94517`. Set

```
q=beta+1=2^B,  J=1,  w=1,  X=q,
D=4*q³*(q+1)/3.
```

D is an integer because `q+1` is divisible by 3. By Dirichlet's theorem,
choose a prime `p>3` satisfying `p=1 mod D`. Write

```
h=(p−1)/D,  Y=q³*h,  s=h,
H=4*Y*(X+1)+3=3*p.
```

Let `d=ord_p(2)`, `k=lcm(2,d)`, and `R=B+k`. Then `k` is positive and
even, so R is odd. Both 3 and p divide `2^k−1`, hence

```
H | X−2^R,     X != 2^R.
```

The quantitative window also holds for every such p. Since `p=1 mod 8`,
2 is a quadratic residue and `d | (p−1)/2`. If d is even then `k=d`; if d
is odd, the high power of 2 dividing D gives `k=2d <= (p−1)/2`. Therefore

```
XY − k >= q³*h*(q−2)/3 > B+1,
```

using the fixed q. Thus `R+1<XY`.

Put `a=Y*(X+1)`, `c=psi_(a+2)(R)` and

```
gamma = [3*X*c − 2*(X²−1)]/H.
```

The prior reviewed recurrence identity gives

```
2^R * [3*X*c − 2*(X²−1)]
  = −2*(X−2^R)*(2^R*X+1)  mod H.
```

H is odd, so the quotient defining gamma is integral. It is positive because
`R>=3`, `a>=X`, and `psi_(a+2)(R)>=psi_(a+2)(3)>X`. Hence the direct
trace-congruence relation has positive coordinates but fails the desired
power equality even with the listed divisibility and window conditions.

The checker authenticates beta from its complete pinned compressed and raw
bytes and verifies the actual exponent and elementary inequality. It also
runs an explicit toy instance of this same prime construction. The actual p
and huge Pell ordinate are not constructed: their existence follows from
Dirichlet and the finite multiplicative order, respectively. The rank,
Pell-norm and full-equation assumptions omitted above remain essential.

```
python3 -I -S -B research/current14-trace-current-port-obstruction/check.py > /tmp/trace-current-port.json
cmp /tmp/trace-current-port.json research/current14-trace-current-port-obstruction/result.json
```

Independent external review is recorded in
`../../reviews/current14-trace-current-port-obstruction-independent/`.
