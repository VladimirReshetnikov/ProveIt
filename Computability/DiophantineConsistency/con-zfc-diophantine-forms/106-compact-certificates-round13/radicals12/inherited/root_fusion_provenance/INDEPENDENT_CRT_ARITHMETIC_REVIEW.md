# Independent audit of the 13-integer CRT carrier

This note checks the new carrier and its reduction to the already audited
signed native system. It uses the native determinant calibration and the
standalone adjacent-Pell rational-descent lemma inherited by the main report.
It does not change the machine, coefficient tuple, or inherited calibration.

## Formula and exact measurements

Keep the thirteen coordinates `j,C,z,h,r,v,w,T,c,n,t,p2,p3` and all front-end
formulas from the main construction except the following changes:

```
Y = q*v
Ag = v^2*Pair - 1 - p2^2 - p3*(p3+1)
M = 2*q^2
Lcrt = 4*H+1
U = M*H
P = M*Lcrt = 4*U+M
center = U*(n+V)+P*b0+H*(v-q^2)
```

The five radicands are

```
P^2*Dmain, U^2*Df, U^2*Dtau, U^2*Ag, U^2*Cy/delta.
```

Apply the exact cleared five-root norm with clearing factor `delta^16`.
Its division-free DAG has thirteen unrestricted integer variables, degree
1088, and 195 live binary operations: 41 additions, 122 multiplications,
and 32 subtractions. `build_crt.py` constructs it without modifying the
parent deliverable's builder. The implementation uses `P=4*U+M` and reuses
`q^2`, saving two operations over a direct transcription of `M*Lcrt`.

## Nonnegative guard bootstrap, before using the carrier congruences

Here `q=beta*(6*j+1)+1`, with `beta=2^1064921-1`. Thus `q` is nonzero and
even, and `q=2 mod 3`. Also `W=12*w+4` is nonzero with absolute value at
least four. If `v=0`, then `a=0`, `Delta=3`, and `H=3`. If `v!=0`, then
`|q|>=2`, `|X|>=8`, `|Y|>=2`, and `|a|>=14`. Consequently `Delta>=3`
and `H!=0` for every integer assignment, including assignments that do not
yet satisfy the equation.

`Dmain`, `Df`, and `Dtau` are positive. Write `I=(2*r+1)*c^2`, so
`Q=(Delta*I)^2` and `delta=Q-1`. If `c=0`, then `Q=0` and `Cy/delta=1`.
If `c!=0`, then `Q>=9`, `Df>|c|+1`, and

```
V = Df*(c*T-R)-c
```

has absolute value at least one. Therefore `Cy/delta>=1`. In particular,
`delta!=0` on the entire integer domain. The four non-guard radicands are
strictly positive, and their scale factors are nonzero.

If `Ag<0`, the only imaginary square root in each of the 32 conjugate
factors is the guard root, with a nonzero coefficient. No factor can vanish.
Thus a zero of the cleared norm implies `Ag>=0`, which gives

```
v^2*Pair = Ag+1+p2^2+p3*(p3+1) >= 1.
```

Hence `v!=0` and `Pair>0`. The nearest-square pair-positivity argument
then implies `G>0` and `eta*zeta>0`. This implication is elementary:
`Pair>0` implies `G*(eta*zeta)>0`; if both factors were negative, the
subtracted square would be larger than their product.

The native determinant calibration supplies `|q|>=16`. Set

```
x=|X|>=64, y=|Y|>=16, K=|k|>=2, C0=|c|.
```

The identities `eta+zeta=k` and `c=Y*k+eta`, together with the common
strict sign of `eta,zeta`, imply

```
K*(y-1) < C0 < K*(y+1),       hence C0>30.
```

These bounds use only `Y=q*v`; the stronger congruence on `v` is not used.

## Rational extraction with only the weak scale bound

Divide all root magnitudes by `|U|` and write

```
g = sqrt(Ag)
tau = sqrt(Dtau)
f = sqrt(Df)
mu = |Lcrt/H|*sqrt(Dmain)
yaux = sqrt(Cy/delta).
```

The following strict inequalities are sufficient:

```
g < (8/15)*C0,
tau > 4*C0,
mu > 2*tau,
f > 5*mu.
```

For the first, use `G<q^2`, `eta*zeta<=K^2/4`, and
`Ag<v^2*G*eta*zeta`. This gives `g<y*K/2`, and
`C0>K*(y-1)` gives the displayed bound since `y>=16`.

Put `ell=X*Y^2`. Then

```
K*(x*y^2-1) < tau < K*(x*y^2+1).
```

Since `x>=64`, `y>=16`, and `C0<K*(y+1)`, the lower bound exceeds
`4*C0`. Moreover

```
sqrt(Delta) > (x-2)*y,
3 < |4+1/H| < 5.
```

It follows that

```
mu > 3*(x-2)*y*K*(y-1) > 2*K*(x*y^2+1) > 2*tau.
```

The middle inequality follows uniformly from `x>=64,y>=16`; for example,
`3*(x-2)*(y-1) >= (1395/512)*x*y`, whose coefficient exceeds `5/2`.

Finally `f>sqrt(Delta)*C0^2`, whereas
`mu<5*sqrt(Delta+1)*C0<6*sqrt(Delta)*C0`. Since `C0>30`, this gives
`f>5*mu`.

If `c*T-R=0`, then `C0<yaux<C0+1`. The order

```
g, yaux, tau, mu, f
```

is superincreasing: each positive entry exceeds the sum of all preceding
entries. If `c*T-R!=0`, then

```
yaux > |V| >= f^2-C0 > 2*f,
```

and the superincreasing order is

```
g, tau, mu, f, yaux.
```

If `g=0`, omit it; it is already an integer. Thus no nonempty signed sum
of the nonzero root magnitudes is zero. The standard multiquadratic
character argument forces every root appearing in a rational sum to be
rational. Since the equation gives an integral such sum, all five roots
are rational.

`Dmain,Df,Dtau,Ag` are integer radicands, so their rational square roots
are integers. Apply the standalone adjacent-Pell rational-descent lemma
to

```
(Delta*I)^2*V^2 - ((Delta*I)^2-1)*yaux^2 = 1
```

to obtain `yaux` integral. This step must precede reduction of the carrier
modulo `M` and `H`; it uses no `q^3` scale condition.

## The carrier restores both missing congruences

Since `H=4*(X+1)*q*v+3`, we have `H=3 mod q`. Since `q=2 mod 3`,
`gcd(H,q)=1`; since `H` is odd, `gcd(H,M)=1`. Also
`gcd(H,Lcrt)=1` because `Lcrt=4*H+1`.

After integer extraction, some signed choice of the five roots satisfies

```
U*(n+V)+M*Lcrt*b0+H*(v-q^2)
  = M*Lcrt*D + U*(signed f + signed tau + signed g + signed yaux),
```

where `D^2=Dmain`. Reducing modulo `M` yields

```
v = q^2 mod 2*q^2.
```

Thus `v=q^2*(2*vold+1)` for an integer `vold`, and
`Y=(2*vold+1)*q^3` is exactly the old scale condition. Reducing modulo
`H` yields `D=b0 mod H`, restoring the old main carrier.

The remaining formulas coincide with the audited normalized-strong and
quotient-fusion construction. The positive `Pair` has the old three-square
positivity representation existentially, even though the current guard
represents `v^2*Pair`. Thus the old kernel is recovered without any new
coordinate in the displayed equation.

## Completeness

Start with a canonical old-system witness and set
`v=q^2*(2*vold+1)`. Choose `t` with `Pair>0`, and represent the positive
integer `v^2*Pair` as

```
1+g^2+p2^2+p3*(p3+1).
```

The standard three-square positivity representation supplies these integer
witnesses. Retain the old integer roots and choose its signed main root
`D` with `D=b0 mod H`. Define

```
n = Lcrt*(D-b0)/H + f+tau+g+yaux-V - (v-q^2)/M.
```

Both displayed quotients are integers, so this is a valid integer value of
the existing coordinate `n`. The corresponding conjugate factor vanishes,
and therefore the cleared five-root norm is zero.

## Exact degree certificate

The relevant degrees are

```
deg(delta)=22, deg(U)=6, deg(V)=19, deg(center)=25,
deg(d)=22, deg(A)=26, deg(B)=34, deg(e)=42, deg(Cn)=72.
```

Writing `center=U*V+s`, with `deg(s)=11`, gives an exact cancellation in
the scalar component of the inner cleared three-root norm. The independent
sparse polynomial audit finds the biquadratic weighted component degrees

```
J:  [64,58,68,54]
K:  [136,122,132,126]
F8: [272,258,268,262].
```

The entire degree-272 leading component is the scalar
`16*delta^4*U^4*V^4*e^2`. Each of the last two conjugate norms squares
this unique highest component, giving degree 1088. With

```
q0=6*beta*j,
a0=12*w*v*q0^2,
i0=2*r,
R0=q0^4*z-12*q0^3*w*C,
k0=R0+h*a0,
eta0=-q0*v*k0,
```

the exact leading form is

```
2^112*q0^64*a0^128*i0^64*c^128*R0^16*v^16*eta0^32.
```

Its selected coefficient at
`j^480*w^160*v^208*h^32*r^64*c^128*z^16` is exactly
`2^976*3^640*beta^480`, which is positive for the actual fixed numeral.
The full leading form has 1,089 nonzero monomials. `check_crt.py` checks
these polynomial statements exactly and separately performs 45 finite
transcription diagnostics with the actual fixed coefficients.
