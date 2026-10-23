# Eleven-variable reduction: proof guide and independently reviewed argument

Baseline inspected: ProveIt commit `124c07c0b77a9e20e84676514d8b1ff78536ea3f`.
The complete algebraic proof, including exceptional-root recovery and the
scalar norm identity, is in Sections 4--7 of `../report.tex`. The independently
reviewed argument below records the key inequalities and their noncircular
order. Inherited ordinary proofs are preserved under `../provenance/`.
This is ordinary mathematics, not a new end-to-end Lean certificate.

## Parameters

Use the common eleven positive coordinates
`J,F,alpha,z,i,T,s,w,eta,zeta,t`, the complete authentic fixed compiler tuple,
and all common definitions of package 44 with `Y=s*q^3`, without an s shift
and without the old coordinate h. Put

```
k=eta+zeta; c=kY+eta; a=E+Y; H=4a+3; E=XY;
I=i*c^2; G=1+Delta*c^2; D=1+Delta*I^2;
Q=Delta^2*I^2; d=Q-1; b=c+R*D; v=c*T;
ell=E*k*Y; A=1+ell*(ell+k); b0=X+a*c;
U=4*q^4; r=k-R-1; K=I*T;
S=H*U; L=U*(1+H*K);
W=U*(b0+H*(t+b+ell))+H*(2*q^4)*k-H*r.
```

The norm is the product over the formal signs of g,tau,f of

```
d*(W-L*g-S*tau)^2-S^2*e+S^2*Baux*f,
g^2=G, tau^2=A, f^2=D.
```

The two formal Pell-root symbols in the inner norm add no supplied
unknowns. Denote the norm by N. The single polynomial is
`Nt*(1+N)-1`, with the common transport factor Nt.

The quotient expression below is notation for the proof only:

```
delta=ell+k/2,
(W-L*g)/S=t+b+delta-r/U+(b0-g)/H-K*g.
```

All supplied polynomial coefficients in S,L,W are integers, since U is
even as a polynomial and the displayed 2*q^4 is exactly U/2. The
equivalent globally doubled carrier is valid but unnecessary.

## 1. Bounds before recovering roots

The unchanged mod-4 norm guard proves N=0 and Nt=1 from a product root.
The weak authentic interface then gives q>=16, 3q<R<q^4-2, X>=q,
Y>=q^3, E>=q^4, k>=2, kY<c<k(Y+1), I>=c^2 and a+2<2E.
No assertion k>E is available or used at this stage.

For positive real g=sqrt(G), f=sqrt(D), tau=sqrt(A), the bounds
`1<A<Delta*I`, `g>tau`, `b+cf<6E^3I^2`, and
`d>(1/2)E^4I^2` use only those weak hypotheses. The exact identity

```
(I*g)^2-(c*f)^2=I^2-c^2
```

gives

```
I*g-c*f > I/(8*E*c).
```

Consequently `d*(I*g-c*f)>E^3*I^3/(16*c)>6E^3*I^2>b+cf`, because
`I/c>=c>2Y>=8192>96`.

For every coherent auxiliary root y, even a complex one, the package-44
estimate gives, with Z=b+Tcf,

```
|y| < Z+Z/d <= b+Tcf+T(b+cf)/d < b+I*T*g.
```

Thus every root x of the inner polynomial satisfies
`|x|<b+ITg+tau`. This avoids the invalid use of the stronger
`Ig-cf>1` before k>E has been recovered.

## 2. Main-root selection with the half carrier

Since k>=2,

```
delta^2-A=k^2/4-1>=0,
0<=delta-tau<k/(8EY).
```

The last bound follows by rationalizing delta-tau and using
delta+tau>2ell=2EkY. Equality in the first line is allowed at k=2.
No absolute bound by one is claimed: k need not be small. Instead,
the already established gap satisfies

```
Ig-cf>I/(8Ec)>=c/(8E)>kY/(8E)>k/(8EY)>delta-tau.
```

If the main sign is negative, its inner argument is

```
x=t+b+delta-r/U+(b0+g)/H+ITg.
```

Here H<5a, g>ac, and b0>ac, so
`(b0+g)/H>2c/5>k`, since c>kY and Y>=4096. As r/U<k, the expression
is greater than `b+ITg+tau`, contradicting the root bound. Thus the
negative main branch is impossible. Actual quadratic conjugation now
forces g to be an integer; x is rational. This does not assume
independence of the square classes.

## 3. Inner roots and parity

The package-44 exceptional-root argument applies unchanged because
`1<A<sqrt(Q)`. It excludes x=0 and C(x)=0 by reducing an integer
identity modulo Q. Its displayed rational formulas recover integral
tau and f. Rational Pell saturation makes y integral, hence x integral.

The first Pell equation has base P0=2EY+1 and gives

```
|tau|=chi_P0(n), k=2*psi_P0(n), n>=1.
```

In particular k is even. This parity is proved before asserting that
delta is an integer. The carrier identity then gives `U | H*r`.

## 4. Why the main rank argument needs no s shift

The main Pell root gives `c=psi_(a+2)(p)` with p>=2, since c>1.
If n=1, then k=2, eta=zeta=1 and c=2Y+1. But p>=2 would give
`c>=2(a+2)>2Y+1`, a contradiction. Hence n>=2 and

```
k>=4P0>8EY,
c>8EY^2>2R,
c>X.
```

All the rank bounds formerly supplied by the s shift have now been
recovered from the two integral Pell equations themselves.

For the strong Pell index m, the divisibility c^2|I gives p|m and
then c|(m/p), by the quotient sequence modulo c. Thus pc|m and m>2p.
The odd auxiliary index j0 obeys j0=+/-p mod m and j0=+/-R mod c.
Because 0<p,R<c/2, the congruences imply p=R.

The signed reduction is valid: reducing 2j0 modulo 2m and reflecting
into [0,m] gives a signed Pell abscissa. A negative representative cannot
equal chi(2p) modulo chi(m), since `2chi(m-1)<chi(m)`. Strict growth
then forces the representative to be 2p.

## 5. Small modulus and exact restoration

As H=4s*q^3*(wq+1)+3, H is odd. Every prime divisor of q other than
3 is coprime to H. If 3|q, then H=3 mod 27, so v3(H)=1. Consequently

```
gcd(U,H) is either 1 or 3,
mu=U/gcd(U,H)>=4q^4/3>R.
```

The recurrence gives `psi_P0(n)=n mod(P0-1)`, hence
`k=2n mod 4EY`. Since `U=4q^4 | 4EY=4w*s^2*q^7`, the recovered
condition U|Hr implies `2n=R+1 mod mu`.

Since P0>a+2 and c>k, monotonicity gives n<p=R. Therefore
`|2n-R-1|<R<mu`, forcing the exact equality `2n=R+1`.
Now r is divisible by 4EY and hence by both E and U. Set h=r/E.
The standard argument gives h>0, and the divided carrier gives
`g=b0 mod H`. Since c>X, gamma=(g-b0)/H is positive.

Every equation of the inherited normalized signed-quotient compiler
has therefore been reconstructed, in a noncircular order.

## 6. Completeness and positive carrier

For a canonical normalized compiler witness take positive g,tau,f,y,gamma.
The old index equation and Pell recurrence give r divisible by 4EY, so
r/U is a positive integer. Define

```
t=gamma+ITg+tau+y-b-delta+r/U.
```

Because y>=b-Tcf,

```
t >= gamma+T(Ig-cf)+(tau-delta)+r/U > gamma+r/U >0.
```

Its integrality uses even k, already a canonical Pell consequence.
The carrier identity then makes a coherent norm factor vanish. Thus
the new equation and the original compiler source have equivalent
existence of positive solutions.

## 7. Independent leading-form check

The scalar circuit inspected is
`eleven/build.py`, midpoint
carrier. Its S,L,W definitions equal the undoubled formulas above by
distributivity. The norm is unchanged by the proof-only notation delta.

Let a subscript zero denote leading forms, and abbreviate
`B0=R0*E0^2*I0^2`, `V0=I0*T*ell0`. Remove the factor U0^16 temporarily.
Four unmatched formal-sign factors have degree 119 and leaders
`-sg*4*H0^2*d0*B0*V0`, with each sg occurring twice.
The four matched factors have the following degrees and leaders:

```
107, 4*H0^2*d0*B0*ell0   (sa=-1, sg=+1)
107, 4*H0^2*d0*B0*ell0   (sa=-1, sg=-1)
101, 4*H0*d0*B0*ell0     (sa=+1, sg=-1)
 97, H0^2*d0*B0*(2t-i*T*c0/E0)  (sa=+1, sg=+1).
```

The degree-101 branch uses b0+g with leading form 2ell0, whereas
b0-g has degree five. The last branch is instead governed by t and
`ITg-Tcf`, whose leading form is `i*T*c0/(2E0)` and degree one.
The two squared-term cancellations are exactly the inherited identity
`d*I^2*G-Q*D*c^2=Q*(I^2-c^2)-I^2*G`.

The residue r/U has degree zero, so it does not affect any of these
leaders (the lowest surviving linear-root degree is one).
Multiplying the leaders yields

```
U0^16 * 2^14 * H0^15 * d0^8 * B0^8 * V0^4 * ell0^3
  * (2t-i*T*c0/E0).
```

It is a nonzero homogeneous polynomial after cancellation of E0 in
the prefactor. Its degree is 64+888=952. The transport factor has
nonzero degree-two leader, giving exact product degree 954.
This independently agrees with the emitted degree certificate. The
literal circuit ledger has 115 binary arithmetic operations; its two
systems have 111 and 110 operations, respectively.

## Audit conclusion

No local mathematical defect was found in this combined reduction.
The degree-954/115-operation equation and degree-952 systems agree
with the scalar definitions and the independent leading-form analysis.
The unbounded native compiler, signed-quotient interface, and K215
syntactic-refutation calibration remain inherited dependencies.


## Full-carrier comparison variant

The optional full variant uses the same eleven variables, fixed tuple,
root-gap estimate, small modulus, and norm evaluator. Replace the midpoint
carrier by

```
K=1+IT,
delta_full=(a+2)*c-ell,
S=UH,
L=U+S*K,
W=U*(b0+H*(t+b+delta_full))-H*r.
```

The quotient argument is

```
(W-L*g)/S=t+b+delta_full-r/U+(b0-g)/H-(1+IT)*g.
```

Here delta_full is a positive integer at every positive assignment.
In the negative main branch, the extra term delta_full+g exceeds tau
because g>tau, while (b0+g)/H>k>r/U. Thus the same complex-root bound
excludes this branch. Rational recovery and index restoration proceed
exactly as in the midpoint proof. Evenness of k is again available from
the first Pell equation, although delta_full does not require it.

For completeness choose

```
t=gamma+(1+IT)*g+tau+y-b-delta_full+r/U.
```

Since y>=b-T*c*f, it suffices that g+tau-delta_full>0.
Indeed g>(a+1)c gives

```
g+tau-delta_full > ell+tau-c >0,
```

because ell=EkY>c under the weak source bounds. Together with the already
positive T*(Ig-cf), gamma and r/U, this proves t>0. Hence the full variant
has exactly the same positive-solvability interpretation.

The unscaled degree calculation and its cancellation proof are the full
carrier calculation in `../provenance/parents/44-POSITIVE_PROOF.md`,
Section 8. Its norm has degree 892 and nonzero leading form

```
-2^14 * H0^16 * d0^8 * B0^8 * V0^4 * ell0^2 * k0 * Y0^2
    * (2*t+k0-i*T*c0/E0).
```

The new norm is U^16 times that norm with t replaced by t-r/U.
Since r/U has total degree zero, it leaves the highest homogeneous part
unchanged. Thus the full norm has degree 956, and its transport product
has exact degree 958. The literal circuit has 116 live binary operations.
The nonzero fixed-instance leading coefficients are also checked by
complete finite-field polynomial arithmetic in `check.py`.

## File and source interpretation

Paths in the generated eleven-variable JSON are relative to that JSON
file; the coefficient binding is `../../coefficients/ports.json`.
The active four-port tuple is package 31 throughout. Historical coefficient
bindings appearing inside preserved parent proofs are source context and
do not replace this tuple. `../provenance/SOURCE_PINS.json` binds all such
verbatim files to the reviewed repository revision.
