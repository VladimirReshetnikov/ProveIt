# Five-unit negative-Pell finalizer: 14 inputs, 75 operations, degree 107

This **proposed** graph has 14 positive inputs, 75 live operations and exact
degree 107 at the authenticated compact44 ports. It changes the finalizer of
the reviewed [`14/78` direct-auxiliary parent](../ordinary14-aux-root78/).
For **all strictly positive integer inputs and arbitrary integer ports with
`beta>0`**, it has exactly the same zero set at the same coordinates as that
parent. The proof and finite graph/degree checks below are submitted for
independent review. This is not a new Lean/iPRA theorem, PDF/JSON binding,
fresh provider replay or global minimum claim; the parent's compact44
endpoint and source qualifications are inherited.

## Five integer-unit factors

The parent is the sum

```
A0² + A1² + (Fa−1)² + g72² + guard²,
```

where its direct first residual satisfies

```
A0 = r²−(1+ell*(ell+k)),  ell=m*k,  m=X*Y²,  k=eta+zeta.
```

Use instead

```
F0 = r²−ell*(ell+k), F1=1+A1, Fs=1+g72, Fg=1+guard,
out = F0*F1*Fa*Fs*Fg−1.
```

For every positive input, `F0=1+A0` and `F0` cannot be −1. Indeed,
`q=1+J*beta>=2`, `X=q*w>=2`, and `Y=q³*s>=8`, so `m>=2` and
`k>0`. The elementary negative-Pell lemma below rules out
`r²−m*(m+1)*k²=−1`.

Independently of input signs or ports, the other three **restricted**
factors are never −1 modulo 4. Write

```
Delta=a²+4*a+3, Q=Delta*(f²−1), I=i*c²,
A1=Dstar²−U²*(1+Delta*c²),
Fa=y²−Q*(y²−V²), g72=I²−Q.
```

Since Delta is 0 or 3 modulo 4, `U²*(1+Delta*c²)` is 0 or 1;
therefore `F1=1+A1` is 0, 1 or 2 modulo 4. Both Delta and `f²−1`
are 0 or 3, so Q is 0 or 1. Hence Fa is congruent to y² or V² and is
0 or 1, while `Fs=1+I²−Q` is 0, 1 or 2 modulo 4.

If the product output vanishes, all five integer factors are units ±1.
The four exclusions force F0=F1=Fa=Fs=+1, and their product then forces
Fg=+1 as well. Thus `A0=A1=guard=g72=0` and `Fa=1`, so the parent's sum
of squares vanishes. The converse is immediate. **Fg need not exclude −1**:
it is the only unrestricted unit factor, so the other four signs determine it.
This is a pointwise positive-domain equivalence, not an all-integer claim.

## Elementary negative-Pell exclusion

We prove that for integers `m>=2` and `k>=1` there is no integer r with

```
r²−m*(m+1)*k² = −1.                                    (1)
```

Suppose otherwise and choose a solution with least positive k, taking
r to be the positive absolute root. If k is even, (1) says `r²=3 mod 4`,
impossible. If k=1, then
`m² < m²+m−1 < (m+1)²`, also impossible. Hence k is odd and at least 3.
Put `D=m*(m+1)` and define

```
r' = (2m+1)*r − 2*D*k,
k' = (2m+1)*k − 2*r.
```

Because `r²−(m*k)²=m*k²−1>0`, we have `r>m*k` and therefore `k'<k`.
Also `((2m+1)k)²−(2r)²=k²+4>0`, so `k'>0`. Finally,

```
((2m+1)r)²−(2*D*k)² = D*k²−(2m+1)²
                            = D*(k²−4)−1 > 0,
```

so `r'>0`. The identity `(2m+1)²−4D=1` gives
`r'²−D*k'²=r²−D*k²=−1`, contradicting minimality of k. The hypothesis
`m>=2` matters: `m=k=r=1` solves (1).

## Count and exact degree

The checker reconstructs the parent graph delta. It removes the original
five-square finalizer's ten gates and the first residual's `1+ell*(ell+k)`
and subtraction gates, then adds nine gates for the five-unit product.
Thus `78−10−2+9=75`. All 14 inputs, four fixed leaves and 75 gates are
live. The first factor directly reuses the existing squares `r²` and
`ell*(ell+k)`; it does not compute `1+A0` as an extra pair of gates.

At fixed ports `deg F0<=22`. The reviewed main and direct-auxiliary bounds
are `deg F1<=30`, `deg Fa<=30`, `deg Fs<=22`, and the linear guard has
degree at most 3. Hence the product output has degree at most 107. Its full
all-inputs-equal ray at authenticated P72/P115 ports modulo 1,000,000,007
has degree 107 and leading coefficient 419359493, proving exact specialized
integer degree 107.

The checker pins both complete graphs and port bindings, checks topology and
liveness, exhausts small modulo-four controls, checks no negative-Pell
solution for `2<=m<=100`, `1<=k<=2000`, and tests 160 positive signed-port
assignments. These finite checks do not replace the unbounded descent above.

```
python3 -I -S -B research/ordinary14-negative-pell75/check.py > /tmp/negative-pell75.json
cmp /tmp/negative-pell75.json research/ordinary14-negative-pell75/result.json
```

Independent external review is recorded in
`../../reviews/ordinary14-negative-pell75-independent/`.
