# A partially signed ordinary-strong core and a quartic in62 integer variables

This note first derives its formulas for the inherited four-port arithmetic interface of `06-blank67`; references below to that package's exact coefficients describe this initial derivation. The accompanying report proves transfer to the new four-site recipe, with the final default binding in `../COEFFICIENT_BINDINGS.json` selecting the package-root recipe `compiler/tshape_constants.json` and its shifted MF mask.

This is an extension of `LOW_DEGREE_PROOF.md`, not an invocation of the
positive source theorem on a signed tuple. It explicitly redoes the
steps that need signs. Constants are the exact four ports of package06.
The imported ordinary strong rank lemma is package02's
`PELL_INTERFACE_LEMMAS.md`; power and population recovery are the
input-independent estimates in the signed-quotient scout and the blank
compiler theorem in package06.

## 1. Domain of the signed32-variable core

Take the23 quadratic equations in `quartic32.json`, but impose positivity
only on these ten primary coordinates:

```
J,F,alpha,z,i,s,w,eta,zeta,gamma.
```

Allow the six primary coordinates

```
f,h,o,j,tau,y
```

and all16 register coordinates to be arbitrary integers.
This signed system is solvable exactly when K215 halts blank.

### Forced signs and pretyping bounds

The first equations force q>=B>=16, L=q^2-1>0, N=q^3>0, X=wq>0,
Y=a-E=sN>0, E=XY>0, a=E+Y>0 and c=kY+eta>0, with k=eta+zeta>0.
Thus H=4a+3>0, Delta=a^2+H>0 and D=X+ac+gamma H>0.
Also C2=c^2>0, I=iC2>1 and Baux=I^2>1.

Transport is unchanged. Since z>=1,F>=1, if C=q-F-alpha<=0 its
left side is at most0, contradicting its required value1. Thus C>0,
F+C<q and G=(q-1)(q-F)+alpha>0. Define R=jc-V. Packing forces

```
R=G(q^2-1)+(MC+q MF)J,
(2q-1)(q^2-1)<R<q^4-q^3,
E>=q^4>R+2.
```

The index equation now reads `k=R+1+hE`. Since k>0, a negative h
would imply `k<=R+1-E<0`. Consequently **h>=0 is forced**, and
`k>=R+1`. Positivity of h itself is not needed anywhere below.

The first norm has `tau^2=1+Lfirst(Lfirst+k)>1`; hence tau is nonzero.
Use |tau| to classify it: k=2 psi_P(n), P=2XY^2+1, n>=1.
Reduction modulo E yields 2n=R+1 modulo E. Because 0<R+1<E,
n>=(R+1)/2>=24. The positive main root gives
D=chi_A(p), c=psi_A(p), A=a+2, and p>n. Pell growth gives
c>A Delta^2 and c>2p; moreover c=kY+eta>2R.

Strong equality is `(ic^2)^2=Delta(f^2-1)`. Since its left side is
strictly positive, f^2>1. Apply the ordinary strong rank theorem to
|f|. It gives

```
|f|=chi_A(m), p|m, c|m, I=ic^2=Delta psi_A(m), m>=c>2p.
```

The estimate |f|>c^2/sqrt(Delta)>2c is also valid.

### Signed auxiliary root and exact target index

The last equations imply

```
I^2 V^2-(I^2-1)y^2=1,
V=of-c=jc-R.
```

They exclude V=0 and y=0 because I>1. Pell classification of the
absolute coordinates gives an odd ell=2u+1 with

```
|I V|=chi_I(ell), |y|=psi_I(ell),
V=epsilon Q_u(I^2), epsilon=sign(V),
Q_u(0)=(-1)^u ell,
Q_u(-Delta)=(-1)^u psi_A(ell).
```

The index ell is odd because I divides chi_I(ell), while even-index
chi values are plus or minus1 modulo I. Both source congruences
survive arbitrary signs of o,j,f:

```
V=-c modulo |f|,       V=-R modulo c.
```

Since I^2=Delta(f^2-1)=-Delta modulo |f|, square the first congruence
and apply the Pell doubling identity to obtain

```
chi_A(2ell)=chi_A(2p) modulo chi_A(m).
```

The signed chi step-down lemma with 0<2p<m gives
ell=plus or minus p modulo m, hence modulo c. The second congruence
and c|I then give R=plus or minus p modulo c. Because 0<R,p<c/2,
the only possibility is **p=R**.

No positivity of f,o,j,V or y was used, and no such sign is silently
supplied by calling a positive-parent theorem.

Finally write 2n=R+1+vE with v>=0. If v>=1, then
2n>=R+1+E>2R, contradicting n<p=R. Thus 2n=R+1 and R is odd.
In fact h is now strictly positive: k=2 psi_P(n)>2n=R+1 since
n>=24 and P>1. Hence hE=k-R-1>0. Its initial sign constraint was
unnecessary; strict positivity has been recovered in a noncircular order.

### Exterior decoding does not inspect auxiliary signs

The input-independent lower Pell-ratio estimate and the main-root
congruence yield X=2^R. Since q divides X and R>3q, q is dyadic and
q^3 divides X. The exact half-binomial extraction depends only on this
odd R and on kY<c<k(Y+1), not on the sign of V. It gives
v2(Y)=popcount(R)-2, hence popcount(R)>=3 log2(q)+2.
The repunit relation gives q=B^N. With

```
S_word=C-1+qF,
T_word=MC J+1+q(MF_native J-1),
R=(q^2-S_word)(q^2-1)+T_word,
```

the native inverse-population lemma recovers the exact two bit masks.
The transport identity and fixed coefficient bounds then recover the
valid periodic blank tableau, hence a blank halting K215 run, exactly
as in package06. These exterior steps use no auxiliary sign.

If preferred, the explicit lower/upper ratio estimates in sections2-4
of `complete84_signed_quotient_soundness_scout.md` can be copied with
its Z replaced by the present C. Its input section is irrelevant here.
This argument does not apply the whole ordinary-input complete84
compiler theorem to the altered inputless constants.

Completeness is immediate from the already proved positive32-variable
construction: allowing more signs discards no positive solution.

## 2. Ordinary quartic over Z with62 variables

Keep all32 core variables as unrestricted integers. For each of the
ten positivity-constrained primary variables x introduce three new
integer variables u_x,v_x,w_x and impose

```
x=1+u_x^2+v_x^2+w_x(w_x+1).
```

The right side is positive for every integer triple. Conversely it
represents every positive integer x: apply Legendre's three-square
theorem to 4(x-1)+1, a positive integer congruent1 modulo4. In a
three-square representation exactly one entry is odd and two are even;
writing them as 2w+1,2u,2v gives the displayed expression.

There are32+10*3=**62 unrestricted integer variables** and23+10=**33
quadratic equations**. The sum of their squares is one ordinary
integer-coefficient quartic polynomial. Its degree is exactly4 because
the coefficient of tau^4 is1. Every solution projects to a partially
signed core solution, hence a K215 halting run. Every positive core
solution extends using the surjective positivity representation.

Consequently ZFC proves that this62-variable quartic has no integer
solution if and only if Con(ZFC). It improves the83-integer-variable
quartic delivered in package04 under this specific metric. No global
variable minimum or new universal bound is claimed.

`integer_quartic62.json` contains all33 expanded residuals; the
generator and exact degree/liveness check are `integer_quartic62.py`.
