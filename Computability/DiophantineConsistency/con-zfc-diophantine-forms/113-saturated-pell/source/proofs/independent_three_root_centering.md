# Strong Pell dominance and a quadratic transport parameter

## Scope, notation, and inherited interfaces

This note proves the semantic reduction for the proposed ten-positive
equations. The intended literal evaluators have the measured profiles
98 operations / degree 358 and 100 / 354 on the `X=wq` chart, and
104 / 330 and 106 / 327 on the direct chart. Those counts and degrees
must be bound separately to the exported circuits. The mathematical
argument here is independent of operation accounting.

The fixed coefficient tuple is the entire coherent tuple of the pinned
`candidates/ten-positive-zero-offset` parent (or its complete, separately
calibrated BFS tuple). Its four ports satisfy

```
beta odd, beta>=31, K0>0, 0<MC<beta<MF<2beta.
```

All ten displayed inputs are strictly positive integers. Retain every
parent polynomial definition except the transport parameter and the
integer carrier center. In this note `A` is the FULL Pell parameter,
one greater than the literal `Am1` register:

```
q=beta*J+1, mu=q^2+1,
X=wq  (ordinary chart), or X=q+x (direct chart),
C=q-F-alpha, k=eta+zeta, c=kY+eta,
A=mu*Y*(X+1)+1, Delta=A^2-1,
I=i*c^2, Df=1+Delta*I^2, Q=Delta^2*I^2, delta=Q-1,
V0=X*mu^2*Y^2, Dtau=1+V0*(V0+1)*k^2,
R=[(q-1)(q-F)+alpha]*(q^2-1)+(MC+q*MF)*J,
Tprime=T+alpha, b=c*Tprime-R, V=Df*b-c,
H=4A-5, Kpos=X*(3c-2X)+2, e=k-R-1.
```

The retained three-root finalizer has normalized roots

```
3*tau, f, y,
tau^2=Dtau, f^2=Df, y^2=(Q*V^2-1)/(Q-1).
```

The following **precise inherited ordinary lemmas** are used. They are
the same interfaces as in the accepted zero-offset99 and direct-zero105
proofs and the cited source61/Pell proof, not new assumptions about an
actual solution existing.

1. For the unchanged positive kernels, vanishing of the retained weighted
   norm yields a rational signed-root equation and makes `tau,f,y`
   positive integers. The proof uses the unchanged radicand separation
   and adjacent-coefficient Pell descent. It is independent of the chosen
   rational center and of the transport parameter `L`.
2. Before transport or projection, the strong/auxiliary folding lemma
   gives `c=psi_A(p)` for an odd positive integer `p`. The first Pell
   equation gives `k=2*psi_P(n0)`, with `P=2*V0+1` and `n0>=1`.
3. The source61 rank/index lemmas apply once `C>0` has given the usual
   bounds on `R`. With `c^2|I`, `V=-c (mod f)`, and `V=-R (mod c)`, they
   recover `p=R`; the unchanged parity, index, whole-product projection,
   and source reconstruction steps then apply. Their only relevant
   finalizer input is the indicated rational carrier relation modulo
   integers.
4. A finite refutation supplies the canonical native outer witnesses,
   the same zero-offset first and main Pell witnesses, a positive strong
   pair `I,f` with `c^2|I`, and the explicit source61 auxiliary witness
   described in the completeness section below. It has `R=3 (mod 4)`,
   canonical nonnegative transport quotient, and `mu^2|e` with `e>=0`.
5. The complete source61/native/controller calibration is the parent's
   ordinary, arithmetizable equivalence between its source solutions and
   finite syntactic ZFC refutations. The coherent tuple is preserved; no
   individual original/BFS coefficient is interchanged.

Adding an integer polynomial to the normalized center changes neither
the three radicands nor any of these separation hypotheses. The changed
transport proof and the required positive completeness are supplied
below. No end-to-end Lean/Rocq theorem or encoded object-ZFC derivation is
claimed by this note.

## 1. The new centers and the literal arithmetic identity

Set

```
Cf=(A+1)*I, Ct=(V0+1)*k, L=k*Tprime.
```

The **strong-only** form adds `Cf` to the parent's carrier center
`n+V`; the **both-centers** form adds `Cf+3Ct`. In all other respects
the polynomial is the retained weighted three-root norm with this
new center and new `L`.

The displayed `Delta` is a proof abbreviation. In the new evaluator one
can compute its necessary products more economically by the exact ring
identities

```
S=(A-1)*Cf=Delta*I,
Df=S*I+1,
Q=S^2.
```

This is valid for every assignment, not merely on solutions. It allows
the old private `Delta` and `I^2` registers to disappear when they have
no other live uses. It introduces no division, square root, variable
exponent, or extra unknown.

The transport identity `W*Bt/(q-1)=L*Bt+Bt/(q-1)`, and its direct-chart
analogue, may be used to simplify the final integer numerator. This
identity already occurs in the supplied dyadic10 package; the new
contribution here is its composition with the following dominance
argument and the new low-degree transport parameter.

## 2. Facts that must precede the transport argument

Since `q>=32`, both charts have `X>=q`, and `Y>=1`, we have `A>4`,
`Delta>mu^2`, and `Delta>8Y`.

At a zero, the inherited first/root folding facts exclude `n0=1`.
Indeed that index gives `k=2`, hence `eta=zeta=1` and `c=2Y+1`.
But `psi_A(1)=1<c<2A=psi_A(2)`, so `c` cannot be any positive main
Pell ordinate. Therefore

```
n0>=2,
k>=2*psi_P(2)=4P=8V0+4,
c>kY>=k>8X*mu^2*Y^2>8q^5.
```

In particular `c>2X`, `I>=c^2>1`, and `Kpos>0`. Also `H>3X>0`.

For clarity the mask bounds used here hold for every positive input,
without already assuming `C>0`. From the port inequalities and
`beta*J=q-1`,

```
0<(MC+q*MF)*J<(2q+1)(q-1).
```

Dropping the negative `-F(q-1)(q^2-1)` term gives

```
R<q^4+(alpha+2)q^2.
```

The negative contribution has magnitude less than `Fq^3`, so also

```
|R|<q^4+Fq^3+(alpha+2)q^2,
|R|/mu^2<F+alpha+1.
```

The second inequality follows directly from
`mu^2=(q^2+1)^2`; after multiplication its difference is

```
F*(q^4-q^3+2q^2+1)+alpha*(q^4+q^2+1)+1>0.
```

Since `c>8q^5` and `Tprime>=alpha+1`, the one-sided bound on `R`
gives `b=c*Tprime-R>0`, hence the integer `b>=1`. Consequently
`V=Df*b-c>=Df-c>1`. No transport sign or projection has been used to
prove this positivity.

The positive auxiliary root therefore satisfies `y>V` and

```
u=y-V
 =(V^2-1)/[(Q-1)(y+V)]
 <V/[2(Q-1)]
 <Df*b/[2(Q-1)]
 <b/Delta.
```

The final strict inequality uses
`Delta*Df=Q+Delta<2Q-2`, which follows from `Delta>=3` and `I>=1`.
Because `c=kY+eta<k(Y+1)<=2kY` and `Delta>8Y`,

```
u<k*Tprime/4+|R|/mu^2.
```

The rational quantity `rho=e/mu^2` has the uniform upper bound

```
rho<k/mu^2+F+alpha+1.
```

No divisibility of `e` is being asserted at this stage.

## 3. One inexpensive strong center absorbs the first root

The first Pell equation gives

```
V0*k<tau<(V0+1)*k.
```

Together with `k>=8V0+4`, this implies

```
3*tau<3(V0+1)*k<k^2<c^2<=I.
```

The strict middle inequality follows from
`3(V0+1)<8V0+4<=k`. The strong equation gives

```
(A-1)*I<f<A*I,
0<Cf-f<2I.
```

Therefore

```
3*tau+f<(A+1)*I=Cf.
```

This proves, uniformly for every pair of root signs,

```
3*eps_tau*tau+eps_f*f-Cf<0.                  (D)
```

The both-centers version has the still smaller expression obtained by
subtracting `3Ct`. Equivalently its first and strong errors are each
negative, because `tau<Ct` and `f<Cf`. This is why it is unnecessary
to keep the parent's large transport expression `HI+b`.

## 4. Soundness of the ordinary `X=wq` chart

Put `Bt=(K0+w)C-F`, `W=1+(q-1)L`, `t=Bt/(q-1)`,
`kappa=Kpos/H`, and `s=Y/q^3`. At this stage the last three named
quantities are rational; only `kappa,s>0` is known.

For the strong-only form the signed factor equation is

```
n=3*eps_tau*tau+eps_f*f-Cf
  +(eps_y*y-V)-kappa-s+W*t+rho.             (N)
```

The both-centers form subtracts the additional positive `3Ct` on the
right. By (D), `eps_y*y-V<=u`, and `kappa,s>0`, every zero satisfies

```
n<u+W*t+rho.                               (U)
```

Suppose `Bt<=-1`.

### Case `C>=1`

Using `C=q-F-alpha`,

```
q(q-F)-C=q*alpha+(q-1)*C>0,
```

so `R>0`. Thus the preceding estimates sharpen to
`u<k*Tprime/4` and `rho<k/mu^2`. Also
`W*t=L*Bt+Bt/(q-1)<-L`. Hence

```
n<k*Tprime/4+k/mu^2-k*Tprime<0,
```

contrary to positive `n`.

### Case `C<=0`

Now `Bt=(K0+w)C-F<=-F`, so `W*t<-F*L`. Equations (U) and the
uniform bounds give

```
n<k*Tprime/4+k/mu^2+2F+2alpha+2-F*k*Tprime. (B)
```

The negative of the right side is

```
D=F*k*(T+alpha)-k*(T+alpha)/4-k/mu^2-2F-2alpha-2.
```

For `k>=8`, this expression is increasing in each of `F,T,alpha`
on the positive integers. Its minimum is therefore at least

```
3k/2-k/mu^2-6>0,
```

because `mu^2>=16`. Thus (B) again contradicts `n>0`.

Both cases are impossible. Consequently `Bt>=0`, and its definition
forces `C>0`, since `(K0+w)C>=F>0`.

## 5. What remains unchanged after transport

The new center `Cf` or `Cf+3Ct` is an integer polynomial. Therefore the
same normalized carrier, reduced modulo integers, is

```
Kpos/H+Y/q^3-W*Bt/(q-1)-e/mu^2.
```

Once `C>0` is established, the inherited bound `3q<R<q^4-2`, the
strong-rank and auxiliary-index lemmas, and the parity argument prove
the same facts in the same order as the zero-offset parent. In
particular they recover `p=R`, then even `q`; the denominator
coprimality then licenses `mu^2|e`. The first-index congruence recovers
`n0=(R+1)/2`. The zero-offset ratio theorem and the strict whole-product
projection recover `X=2^R`, followed by the main integral projection
and the original source data.

It is essential to preserve this chronology: no coprimality of `mu`
with `q-1` is assumed before evenness of `q`, and no factor is cancelled
illicitly from the entire product modulo `H`. The parent proof already
handles those issues; the new integer center does not change their
fractions. Source reconstruction uses the source's own unscaled
parameter `a+2`, as before, not the new scaled `A`.

Thus every new positive zero yields a finite syntactic refutation under
the same complete source/native/controller theorem.

## 6. Completeness with the explicit canonical auxiliary witness

Start from a finite refutation. Keep the parent's canonical native
outer data, the zero-offset first and main Pell witnesses, and a
canonical strong pair `I,f`. In particular

```
c=psi_A(R), R=3 (mod 4), R>=5,
c^2|I, f^2-Delta*I^2=1,
rho=(k-R-1)/mu^2 in Z_{≥0},
t=Bt/(q-1) in Z_{≥0},
s=Y/q^3 in Z_{>0}, kappa=Kpos/H in Z_{>0}.
```

The source61 auxiliary-completeness lemma applies for every `A>=2`;
it does not require even `A`. With

```
S=Delta*I, Q=S^2, R=2v+1,
V*=chi_S(R)/S=Q_v(S^2),
T*=(V*+c+R*f^2)/(c*f^2),
Q*(V*)^2-(Q-1)*y^2=1,
```

its witnesses have positive integral `T*`, `V*`, and `y>V*`. The
retained recurrence estimate gives

```
V*>=(4Q-3)^v>=(3Q)^v>=9Q^2,
```

since canonical `v>=2`. Since `c<S` and `f^2<Q`,

```
T*>V*/(c*f^2)>V*/S^3>=9S>alpha.
```

Thus `T=T*-alpha` is a strictly positive integer, and the literal
register `V` is exactly `V*`. We now set `L=k*T*` and its corresponding
positive `W`.

Because `V*>=2` and `y<2V*`,

```
u=y-V*=(V*^2-1)/[(Q-1)(y+V*)]
       >V*/(4Q)>=9S^2/4.
```

The canonical bounds are

```
k,Y<c<I<S,
0<kappa=Kpos/H<3Xc/H<c<S,
0<Cf-f<2I,
0<Ct-tau<k.
```

For the strong-only equation choose

```
n=3*tau+(f-Cf)+(y-V*)-kappa-s+W*t+rho.
```

It is integral. The negative terms have magnitude less than
`2I+c+Y<4S`, while `u>=9S^2/4>4S`; hence `n>0`.

For the both-centers equation choose instead

```
n=3*(tau-Ct)+(f-Cf)+(y-V*)-kappa-s+W*t+rho.
```

The total negative loss is less than
`3k+2I+c+Y<7S`. The same bound `u>=9S^2/4>7S` holds because the
canonical `S>=4`. Thus this `n` is also strictly positive.

In each case one exact conjugate factor of the retained norm vanishes.
This proves the reverse implication. In particular no unsupported
cofinality or simultaneous-Pell assertion is needed: the already
published explicit auxiliary witness is large enough.

## 7. The direct chart

Retain the parent's direct definitions

```
X=q+x,
B=(q*K0+X)*C-q*F,
Wdir=1+q*(q-1)*L,
P=q^4*(q-1), M=P*mu^2*H.
```

The new normalized center is

```
Z/M=n+V+Cf[+3Ct]+Kpos/H+Y/q^3
     -Wdir*B/[q*(q-1)]-X/q^4-e/mu^2.
```

Initially `X>q` is known, but `q|X` is not. All early root/folding and
mask bounds above remain valid, because they used only `X>=q`, not
the ordinary-chart factorization.

The additional term `X/q^4` in the equation for `n` is absorbed by the
same strong center. Namely `X/q^4<X<k`, so

```
3*tau+X/q^4
 <3(V0+1)*k+k
 =(3V0+4)*k
 <(8V0+4)*k
 <=k^2<c^2<=I.
```

Consequently

```
3*eps_tau*tau+eps_f*f-Cf+X/q^4<0.
```

The both-centers form is smaller still. If `B<=-1` and `C>=1`, then
`R>0` and `Wdir*B/[q(q-1)]<-L`, giving the first contradiction above.
If `C<=0`, then `B<=-qF` and
`Wdir*B/[q(q-1)]<-qF*L<=-F*L`, giving the second contradiction.
Thus `B>=0` and `C>0`.

The direct parent's unchanged chronology then recovers rank, parity,
`mu^2|e`, and the complete product modulo `H` before cancelling that
denominator. The whole-product projection yields `X=2^R`. Only then
does the rational carrier give

```
Y/q^3-Wdir*B/[q(q-1)]-X/q^4 in Z.
```

Reduction of its numerator modulo `q` gives `q|X`. Because `X=2^R`,
`q` is a power of two. The inherited `R>3q` bound gives `q^4|X`.
Now `w=X/q` and `u0=X/q^4` are positive integers, and
`B=q*Bt`; the remaining source divisibilities and native calibration
follow exactly as in the accepted direct proof.

### Positive completeness transfer

One can transfer the corresponding new ordinary-chart zero, just
constructed, to the direct chart without any new witness theorem.
Its soundness gives `X=2^R>q`, `q^4|X`, and `t=Bt/(q-1)>=0`. Set

```
x=X-q>0,
Wbase=1+(q-1)*L,
DeltaW=Wdir-Wbase=(q-1)^2*L>0,
n_direct=n_base+DeltaW*t+X/q^4.
```

This is a positive integer. Every kernel, `Cf`, optional `Ct`, and
the new `L` agrees because the physical value of `X` is unchanged.
The normalized centers coincide exactly. In the integer numerators,
`Z_direct=q*Z_base` and `M_direct=q*M_base`, so all four squared norm
arguments scale by `q^2` and the complete norm value by `q^8`.
Thus the direct equation vanishes. The extra `X/q^4` helps positivity;
it is not an additional loss in the direct completeness argument.

## 8. Logical conclusion and limits

For each new fixed polynomial, the two constructed implications give,
by the same ordinary source calibration formalizable in ZFC,

```
exists positive integer zero <=> exists finite ZFC refutation.
```

Negating yields the requested ZFC-provable unsolvability/Con(ZFC)
equivalence. The argument does not assume Con(ZFC), prove actual
unsolvability, certify global simplicity, or add a completed formal
proof-assistant endpoint. Exact circuit reconstruction and attained
degree certificates are necessary artifact checks, distinct from the
unbounded arithmetic proof above.

The new semantic point is the explicit inequality `3tau<I`: the
otherwise unused strong Pell scale provides a common upper center
for two radicals. Earlier supplied packages already contain radical
centering, quadratic transport majorants, and the distributed transport
identity. Those dependencies should be credited, and the improvement
described as this specific new composition and quantitative lemma.

