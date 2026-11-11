# A q-X main-carrier tradeoff: proposed 84 operations, degree 60

This 14-positive-input probe has **84 live operations and exact degree 60**
at the authenticated compact44 ports. It proposes a positive-zero existence
equivalence with the reviewed 85/56 graph. The reverse map needs the modified
main-carrier calibration below; the argument is submitted for independent
review. It is not a new Lean/iPRA theorem, PDF or JSON file-semantics
binding, independent provider-ancestry replay, or global minimality claim.

Replace the 85 graph's positive X input by positive w and set `X=q*w` inside
the graph. Rename the old positive gamma to `gamma_old` and introduce the
new positive gamma input `gamma_prime`. The 85 graph has `Y=q³*s` and main
shift

```
U*gamma_old+E*q−(k−R−1),  E=X*Y, U=Y*q².
```

With `gamma_prime=gamma_old+w`, `X=q*w` and `Y=q³*s`, `E*q=U*w`; hence
this equals `U*gamma_prime−(k−R−1)`, the new literal shift. All other
residuals and the guard are unchanged. This is an exact commutative-ring
identity, checked on signed-integer controls. The difference between the
positive domains is addressed below.

## 85 to 84

A positive 85 zero maps to a positive 86 zero by the reviewed q-cube
coordinate map. The reviewed external sign-free decoder replay in
`../ordinary14-shifted-guard87-calibration/` applies at the authenticated
ports: it derives `X=2^R` and `q|3X` from the norms and positive scalar
gap. To get `q|X`, the compact44 Mersenne form of beta is essential:
write `beta=2^B−1`, `B=590069>=4`. From `q|3*2^R`, every q has the form
`2^j` or `3*2^j` with `j<=R`. The second form would give
`3*2^j=1 (mod beta)` because `beta|q−1`. Reduce j modulo B to `r<B`. If
`r<=B−2`, the residue is `2^r+2^(r+1)`, strictly between 1 and beta; if
`r=B−1`, it is `2^(B−1)+1`, also strictly between 1 and beta. Both cases
contradict the congruence. Hence `q=2^j` and `q|X`. This is the standard
integer content of `ArithmeticAdaptiveMersenne2011.cancel_three`; the
argument does not claim q divides X merely from gcd(3,X)=1. Set `w=X/q>0` and
`gamma_prime=gamma_old+w>0`. The graph identity gives a positive 84 zero.
This uses the inherited standard-integer calibration, not a new Lean client.

## 84 to 85: modified main carrier

Suppose the new graph has a positive zero. Use

```
b=J*beta, q=b+1, X=q*w, Y=q³*s,
C=q−F−alpha, E=X*Y, m=E*Y, k=eta+zeta,
c=eta+Y*k, a=E+Y, H=3+4*a,
U=Y*q²=q⁵*s, Delta=(a+2)²−1.
```

The guard gives `C*(X+K0)=F+b*h>0`, so C>0, `F+alpha<q`, and R is positive.
The compact44 bytes satisfy `beta>=46`, `K0>=0`, `0<MC<beta` and
`0<MF<2beta`. The scalar rank window gives `R+q³+q+1<=q⁴`. Also `C>0` implies
`G=b*(q−F)+alpha>=2q−1`, so nonnegative masks give `R>=q³>=26`. The first norm gives the usual Pell solution
`tau²=1+m*(m+1)*k²`. The main expression is now

```
Dstar=U*(X+a*c)+H*(U*gamma_prime−k+R+1).
```

It is positive without assuming any old gamma: `U*a*c>H*k` follows from
`c>Y*k`, `Y>=q³`, and `q>=3`. Its main norm gives `Dstar=U*d` with
`d²=1+Delta*c²`. Hence

```
H*(R+1−k)=U*(d−X−a*c−H*gamma_prime).
```

Since `U=q⁵*s` and `H=3+4*q³*s*(X+1)`, the same factor-three cancellation
as in the sign-free decoder yields `q⁴|(R+1−k)`, including when 3 divides q.
Classify the positive first and main Pell solutions by indices n and p. The
first recurrence gives `k=2*n+4*m*v` for some `v>=0`; as `q³|Y`,
`q⁴|4*m`. With the rank window, `mu=q⁴` therefore satisfies
`R+1<mu` and `(2*n) mod mu=R+1`.

The first/main/strong/auxiliary hypotheses of
`P72Exact.indices_ordinary` are mapped exactly as in the reviewed
sign-free decoder: the graph's strong input is `i_prime=i` and its auxiliary
squares are `|V|²` and `|V+u|²`. The modified carrier does not enter that
theorem. It yields `n>=13`, `p=R`, and `2*n=R+1`. Consequently

```
k=R+1+U*W,    W=4*X*q*s*v >= 0,
d=X+a*c+H*(gamma_prime−W).                 (1)
```

The last relation is an integer congruence even if `gamma_prime−W` is not
yet known positive. Since `X=q*w>=q>=47`, all size hypotheses of
`P72Power.power_of_mod` hold; (1) supplies its `d=X+a*c (mod H)` hypothesis.
It gives `X=2^R`.

The reviewed Pell trace identity for `d=chi_(a+2)(R)` then gives

```
d=2^R+a*c+H*gamma0,
gamma0=sum_{j=1}^{R−1} 2^(R−1−j)*psi_(a+2)(j) >= 2^(R−2).
```

Comparing with (1) gives `gamma_prime=gamma0+W`. Since `q>=8` and `X=q*w`,
`w<=X/8<gamma0<=gamma_prime`. Thus
`gamma_old=gamma_prime−w` is a positive integer. With this gamma and the
same positive X, s and remaining coordinates, the exact main-carrier identity
maps the new zero to a positive 85 zero. The positivity is established from
the new norms, not assumed from an old graph zero.

## Count and degree

The literal graph adds `X=q*w`, deletes `E*q` and the addition of that term
to `U*gamma`, and retargets the following subtraction: `85+1−2=84`.
The checker verifies the graph delta, unique topology/liveness, 100 exact
signed substitution controls and the P72/P115 port hashes. All 14 inputs
and four fixed leaves are live.

For a degree upper bound, the new X has degree at most 2, Y at most 4,
`U<=6`, `a<=6`, `c<=5`, `H<=6`, `ell<=11`, `M<=4`, and `R<=4`.
The first residual's square cancellation gives degree at most 20. For the
main residual write `Dstar=U*a*c+Theta`, with
`Theta=U*X+H*(U*gamma_prime−k+R+1)` of degree at most 13; then

```
A1=2*U*a*c*Theta+Theta²−U²*(1+H*c²)
```

has degree at most 30. The auxiliary, strong and guard residuals have degree
at most 23, 22 and 3. The final sum of squares therefore has degree at most
60. The direct compact44 modular ray has degree 60 and leading coefficient
979167194 modulo 1000000007, proving exact specialized integer degree 60.

This trades one fewer operation for degree 60 instead of 56 versus the
14-input 85/56 graph. The displayed PDF equation has fewer operations and
higher degree. These are comparisons to named records, not global optimality
or a new consistency/PDF proof.

```
python3 -I -S -B research/ordinary14-qcube84-probe/check.py > /tmp/qcube84.json
cmp /tmp/qcube84.json research/ordinary14-qcube84-probe/result.json
```

The finite checker does not replace the proposed modified-carrier proof.

Independent mathematical review is recorded in
`../../reviews/ordinary14-qcube84-probe-math-independent/`.
A separate independent decoder review is recorded in
`../../reviews/ordinary14-qcube84-probe-independent/`.
