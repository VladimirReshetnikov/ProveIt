# Complement-port substitution: a positive inverse obstruction

**The literal substitution `u=q-F` does not preserve the parent positive-zero relation.** Its 85-gate graph can have positive zeros with `F=q-u<0`. The construction below supplies such zeros for every positive input x while keeping the valid fixed compiler numerals unchanged. Thus this particular syntactic 85-operation candidate cannot inherit the complete universal86 theorem. The frozen 86-operation source is unaffected.

This is a mathematical source/domain audit, not a maintained 85-operation compiler. The accompanying checker authenticates the actual 86 source/receipt and relevant proofs, verifies the one-gate source substitution and full graph identity, and checks bounded outer and first/main/input components. The astronomical auxiliary Pell tuple is supplied parametrically in the proof; it is not materialized by finite testing. The finite checks support the general source-specific construction below; they do not replace its proof.

## Literal source and the lost bound

In the normalized form of [complete86_factored_first_root](complete86_factored_first_root.md), F has exactly one source consumer: `q_minus_F=q-F`. Replacing that supplied coordinate by a positive u and replacing references to this register by u removes one addition. All remaining rows are literal parent rows. Hence

```
P85(x,u,other)=P86(x,F=q-u,other)
```

on all integer tuples; the paid count is syntactically `48M+37A`. This identity alone does not restore F's positive domain.

Use `q=(B-1)J+1`, `X=wq`, `Y=sq^3`, `E=XY`, `a=E+Y`, `Delta=(a+2)^2-1`, and `H=4a+3`. Let `l=2dx`, `e=l+b`, where the valid fixed input convention has d>=4 and odd e>=3. K denotes the fixed source port `Kconstant`. The changed outer definitions are

```
C=u-Z-alpha-l, W=C-Z,
G=qu-Z,
R=G(q^2-1)+(MC+q*MF_source)J,
Nt=(K+X)C+u-zplus(q-1).
```

Here `MF_source=MF0+B-1`; the actual compiler masks have `0<MC,MF0<B-1`, `MC=2 mod4` and `MF0=4 mod8`.

The old argument `Nt=±1 => C>=0` used `1-F-(zplus-1)(q-1)<=0`. That inequality is unavailable after the substitution. Even proving C>=0 separately would give an upper bound on Z+alpha+l in terms of u, rather than u<q. More seriously, the packed-index upper bound can fail while all eight factors become +1, as follows.

## Phase-constant widths for every fixed cell size

Fix any positive input x and the unchanged valid fixed numerals. Choose an integer L>=max(d,e+1,4), and set

```
t=L!, q=2^t=B^(t/d), J=(q-1)/(B-1).
```

Then d divides t and t>e. Also

```
t divides q(q-1), hence t divides A0=q(q^2-1).
```

To prove the divisibility, write any odd prime-power divisor of t as p^v. Euler's order bound divides `p^(v-1)(p-1)`, and this number divides L!: the p-part has exponent v-1 and p-1 divides L!. Therefore `2^t=1 mod p^v`. The power-of-two part of t divides `2^t`. Combining coprime prime powers proves the displayed assertion. This choice changes an existential width, not a program numeral.

Define the actual shifted remainder

```
Tprime=MC*J+1+q*(MF0*J-1)
      =(MC+q*MF_source)J-q^2+1.
```

The compiler mask bounds imply `0<Tprime<q^2-1` and `Tprime=3 mod4`. Put

```
Z=1, W=2^e, C=W+1,
v=2^(Tprime mod t),
u0 = the least nonnegative residue of 1-(K+v)C modulo q-1.
```

For every u=u0 modulo q-1, the packed expression is exactly

```
R=A0*u+Tprime.
```

Since t divides A0, `R=Tprime mod t`, and therefore the genuine canonical power `X=2^R` has residue v modulo q-1. The transport numerator `(K+X)C+u-1` is divisible by q-1. No numeral K is selected or modified to arrange this congruence.

## Large positive u with the required population

Set

```
h0=8t+8,
u=u0+(q-1)(2^h0-1),
M=A0(q-1), beta=M-A0*u0-Tprime.
```

Because `0<=u0<=q-2` and `0<Tprime<q^2-1`, we have `0<beta<M<q^4=2^(4t)`. Thus

```
R=M*2^h0-beta
 =(M-1)*2^h0+(2^h0-beta),
popcount(R)=popcount(M-1)+h0-popcount(beta-1)>3t+2.
```

The last two blocks are disjoint, and the low block is the h0-bit complement of beta-1. This also makes R positive, R=3 modulo4, R>e, R>3t, and R far larger than q^4. The new u exceeds q and `W+l+2`.

Now supply

```
alpha=u-W-l-2>0,
zplus=((K+2^R)C+u-1)/(q-1)>0.
```

Both are positive integers. The literal source gives exactly C=W+1, W=2^e, R as above and Nt=1. The inverse parent coordinate is **F=q-u<0**.

## Why the positive Pell converse still applies at this large R

The theorem statement in [half-binomial42](pell_kernel_half_binomial42.md) includes `R<q^4` because its *soundness* proof needs that upper bound to recover the actual indices. Its explicit positive witness construction does not need that bound. Here we extend only that positive converse: take q=2^t>=16, R>=3q+1, R>e, R=3 modulo4 and popcount(R)>=3t+2, with no upper bound on R. We construct its witnesses directly and check the quantitative requirements; we do not extend the old soundness theorem or apply its bounded statement outside its hypotheses. The oversized R constructed above meets all these lower bounds.

Put r=(R-1)/2, X=2^R, and

```
Mbin=binom(2r,r)+sum_(j=1)^r binom(2r,r+j)*X^j,
Y=Mbin/2.
```

The central coefficient is even, and all other terms are divisible by X. Hence Y is an integer, `Y>=X^r/2`, and

```
v2(Y)=popcount(r)-1=popcount(R)-2>=3t.
```

So `s=Y/q^3` and `w=X/q` are positive integers. Set

```
a=Y(X+1), A=a+2, Delta=A^2-1, H=4a+3, E=XY,
P=2XY^2+1,
c=psi_A(R), D=chi_A(R),
k=2*psi_P(r+1), tau_root=chi_P(r+1).
```

The standard source estimates, written before exponent recovery in half-binomial42 §5, compare c/k with `xi/2`, where `xi=(X+1)^(2r)/X^r`. At these explicit X,Y, the discarded lower binomial tail satisfies `0<xi-2Y<1/4`; `a>8r` and the required strict lower comparison `6XY^2>a` hold. In particular their upper bound is `c/(k/2)<xi*(1+8r/a)`. Since Y>1 and `xi=2Y+theta<2Y+2`, it gives the explicit chain

```
0<c/k-xi/2 <4r*xi/a
            <4r*(2Y+2)/((X+1)Y)
            <16r/(X+1)<1/2.
```

The last inequality follows from X=2^R and r=(R-1)/2 for R>=15. Also `a=(X+1)Y>8r` follows directly from `Y>=X^r/2`, verifying the small-error premise `4r/a<1/2` of the source estimate.

Thus `Y<c/k<Y+1`. Every inequality is valid with room to spare at our large R; none requires an upper bound on R in terms of q. The paid source's ratio witnesses

```
eta=c-kY, zeta=k-eta
```

are positive. The recurrence modulo E gives the positive integer

```
h=(k-R-1)/E.
```

The first and main norm factors equal one. All definitions use the actual asymmetric `X=wq, Y=sq^3` source. The first norm is `tau_root^2-L0(L0+k)` with `L0=XY^2 k`, exactly the normalized86 first-root factor.

For completeness, use the already proved canonical normalized minus family from [normalized strong87 §3](complete75_normalized_strong87.md):

```
m=2cR, f=chi_A(m), i=psi_A(m)/c^2,
T=Delta*psi_A(m), y_aux=psi_T(R), V=chi_T(R)/T,
o=(V+c)/f, j=(V+R)/c.
```

The division defining i is integral by expanding `(D+c*sqrt(Delta))^(2c)`: its linear term is a multiple of c^2 and every higher odd term contains c^3. R=3 modulo4 supplies `V=-c mod f` and `V=-R mod c`; the positive Pell growth supplies V>c. Thus all four remaining supplied auxiliary coordinates are positive integers. Direct substitution gives the normalized strong and auxiliary factors equal to one and `V=of-c=jc-R`.

## The ordinary input and the shared positive gap split

Take the input Pell pair at its actual fixed-affine index e:

```
kappa=psi_A(e), mu=chi_A(e), delta=(kappa-e)/Delta.
```

Since e is odd, `psi_A(e)=e mod Delta`; since e>=3, delta>0. Define

```
z_n=chi_A(n)-a*psi_A(n), gamma_n=(z_n-2^n)/H.
```

The exponent recurrence gives integer gamma_n. More explicitly,

```
gamma_0=gamma_1=0,
gamma_(n+1)=2A*gamma_n-gamma_(n-1)+2^(n-1)  (n>=1).
```

Therefore gamma_n is positive and strictly increasing for n>=2. Supply `rho=gamma_e` and `sigma=gamma_R-gamma_e`; these are positive because R>e>=3. Then the source computes

```
D=X+a*c+(rho+sigma)H,
mu=W+a*kappa+rho H,
kappa=e+delta*Delta.
```

The main and input norm factors are both +1, with the required shared main gap and both original positive quotient coordinates. This addresses the coupled input port, not merely the isolated packed history.

The exact nineteen supplied child coordinates, in source order, are

```
J,u,alpha,zplus,f,h,i,j,o,s,w,tau_root,eta,zeta,y_aux,Z,delta,rho,sigma.
```

Their formulas and strict positivity were established individually above; no extra supplied root or computed coordinate is omitted from this list. The six fixed numeral ports and the ordinary input x remain unchanged.

Finally, `k=R+1+hE` makes the index factor +1, and `V=jc-R` makes the coupled linear factor +1. The transport factor was already +1. Thus **all eight literal factors of the proposed complete 85 source equal +1**. Every new supplied witness is a positive integer, but its inverse F is negative.

The construction applies separately to every x>0, with the fixed program numerals held fixed throughout. For a proper recursively enumerable input language, this modified source would accept inputs outside that language. The loss is the bounded packed-field representation; positive auxiliary Pell reconstruction does not repair it. The valid 86 source keeps the supplied positive F and excludes these assignments.

## Executable boundary and scope

The helper uses authenticated literal source rows to check the one-addition substitution and full all-value coordinate identity. Its outer fixtures choose moderate t satisfying the proved phase divisibility, check the exact source packing and transport congruence, natural slack, negative restored F, all population identities and unchanged fixed numerals. Separate modest Pell fixtures test the unbounded-converse first/main/input formulas, including indices beyond the toy q^4 upper bound. These checks do **not** materialize a complete auxiliary tower at a valid compiler width; the general construction above is the proof of the full positive zeros.

No source or proof file is changed, and no 85-operation universal bound is asserted. The separate exact-affine census retains its own scope and should link this mathematical obstruction rather than count this coordinate substitution as a valid improvement.

Portable source/component replay:

```
python review_complete86_complement_port_math.py \
  --root /path/to/native-stream-queue \
  --output /tmp/complement-obstruction-replay.json \
  --expect review_complete86_complement_port_math.json
```

The source pins all eight used predecessor source, receipt and proof-note files before reading them; no predecessor module is imported.
