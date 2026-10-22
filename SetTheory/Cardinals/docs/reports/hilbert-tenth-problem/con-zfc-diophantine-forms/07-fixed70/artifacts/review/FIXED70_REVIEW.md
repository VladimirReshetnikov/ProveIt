# Independent review of the fixed 70-operation instance

## Scope and conclusion

The literal `fixed70` packet in `../fixed_input.json` passes this review. It
defines an ordinary integer polynomial in 16 strictly positive integer
witnesses. Its arithmetic circuit has 70 instructions, consisting of 40
multiplications and 30 additions or subtractions. The coefficient recipe is
the finite modified75 compiler instance in `../compiler/COEFFICIENTS.md`.

The important new proof obligation is the use of `(B-1)J` as a repunit before
its sign has been recovered. The argument below resolves that obligation
without assuming the very repunit identity it is intended to prove. The paid
scale `X=wq^2` supplies the required preliminary bounds. The exact degree is
169. This is a construction and review, not a global minimality theorem or a
new proof-assistant certificate.

The independent finite checks in `review_fixed70.py` read the JSON packet and
the emitted normalized machine directly. They do not import either author's
generator or verifier. Their receipt is `independent_review.json`.

## 1. Mathematical transcription of the emitted source

All the following witnesses are strictly positive integers:

`J,F,alpha,t,f,h,i,T,s,w,tau,eta,zeta,y,Z,gamma`.

Here `t` is the transport quotient, `T` is the auxiliary quotient, and `J`
is named `Jrep` in the packet. Let the five fixed numeral ports be
`beta=B-1`, `K=DC+B*DR`, `MC`, `MF=MF_native+B-1`, and `W0=2^b*B^2`.
Define

```
C = Z+W0,       q = C+F+alpha,       e = beta*J,
X = w*q^2,      Y = s*q^3,          E = X*Y,
k = eta+zeta,   c = k*Y+eta,        a = E+Y,
Delta = a^2+4a+3,                  H = 4a+3,
D = X+a*c+gamma*H,                 L = X*Y^2*k,
Galt = e*(q-F)+(q-F-Z),
R = Galt*(q^2-1)+(MC+q*MF)*J,
V = c*(T*f-1)-R*f^2,
Kaux = Delta^2*i^2*c^4.
```

The seven factors are

```
N0 = tau^2-L*(L+k),
Nm = D^2-Delta*c^2,
Ne = q-e,
Na = Kaux*(V^2-y^2)+y^2,
Nk = k-h*E-R,
Nt = (K+w)*C+(q-F)-t*e,
Ns_scaled = Delta*f^2-Kaux.
```

The emitted polynomial is exactly

`P = N0*Nm*Ne*Na*Nk*Nt*Ns_scaled-Delta`.

The equality with the JSON source is by direct substitution of its named
arithmetic rows. As a finite transcription check, the independent script
compares every factor and the final output with these separately written
definitions on 64 signed or positive assignments. These assignments use
small arbitrary coefficients to test arithmetic; they are not compiler zeros.

## 2. Unit recovery and bounds before an exact repunit

At a positive zero, `Delta>0`, so cancellation gives

`N0*Nm*Ne*Na*Nk*Nt*Ns=1`, where `Ns=f^2-Delta*i^2*c^4`.

Every factor is therefore an integer unit. The consecutive-product
negative-Pell descent excludes `N0=-1`. Since `Delta` is 0 or 3 modulo 4,
the main and normalized strong norms cannot be -1. Since `Kaux` is an
integer square, the auxiliary norm cannot be -1 either. Thus

`N0=Nm=Na=Ns=1`, and `Ne,Nk,Nt` initially belong to `{1,-1}`.

Put `epsilon=Ne`. Only `e=q-epsilon` is known at this point. In particular,
neither `q=B^N` nor `e=q-1` may yet be used.

The explicit definitions give `F+Z<q`, `C>W0`, and
`q>W0=2^b*B^2`, hence `q>=16`. Put `delta=q-F` and
`G=q^2-Z-qF=q*delta-Z`. The following bounds use only positivity:

```
2q-1 <= G <= q^2-q-1,
Galt = G+(1-epsilon)*delta,
2q-1 <= Galt <= q^2+q-3.
```

The true compiler masks satisfy `0<MC<beta` and
`0<MF_native<beta`, so the shifted source mask satisfies `0<MF<2beta`.
Consequently

```
0 < (MC+q*MF)*J < (1+2q)*(q+1),
(2q-1)*(q^2-1) < R
  < (q^2+q-3)*(q^2-1)+(1+2q)*(q+1)
  = q^4+q^3-2q^2+2q+4
  < q^4+q^3.
```

The scale change now pays for the larger preliminary interval:

`E=w*s*q^5>=q^5>R+5`, and `a=E+Y>R+2`.

No exact repunit was used in these inequalities. This is the reason the
70-operation construction uses `X=wq^2`, whereas the 71-operation variant
can retain `X=wq` and its separately computed `q-1`.

## 3. Auxiliary positivity and the index sign

The local argument of `complete85_auxiliary_bezout_projection.md`, Sections
3 and 4, remains valid with the preceding bounds. Its inputs are the
individual norm equations and inequalities, not the input Pell block or an
already decoded mask. For clarity, the critical steps are recorded here.

The strong norm gives `f^2=1+Delta*i^2*c^4`, hence `f>c^2>2c`. Since
`R<a<Delta`,

```
Kaux-(R*f^2+c)
  = (Delta-R)*f^2-Delta-c
  >= 1+Delta*(i^2*c^4-1)-c > 0.
```

The auxiliary equation is `Kaux*V^2-(Kaux-1)*y^2=1`. It excludes `V=0`;
any solution with `|V|>1` has `|V|>=2Kaux-1`. But the definition of `V`
gives `V>-R*f^2-c`, which excludes every negative value of that size.
The cases `V=1` and `V=-1` are excluded by `V=-c (mod f)` and `f>2c`.
Therefore `V>0`.

The proof-only restored coordinates

```
o = c*T-R*f,
j = T*f-R*Delta*i^2*c^3-1
```

are integers, with `o*f=V+c>0` and `j*c=V+R>0`. Thus both are positive
before invoking a rank theorem.

Let `A=a+2` and `P0=2XY^2+1`. The first and main Pell equations give

```
k = 2*psi_P0(n),       tau = chi_P0(n),
c = psi_A(p),          D = chi_A(p),
2n = R+epsilon_k (mod E),     epsilon_k=Nk.
```

Since `0<R+epsilon_k<E`, the least-positive-residue argument gives
`n>=(R-1)/2>=24`. Parameter monotonicity, `P0>A`, and `c>k` give `p>n`.
Elementary Pell growth then gives `c>A*Delta^2`, `c>2p`, and `c>2R`.
The normalized strong equation supplies the ordinary strong premise using
`i_ordinary=Delta*i`. The retained signed auxiliary step-down lemma, with
`V=o*f-c=j*c-R`, consequently gives `p=R`.

Write `2n=R+epsilon_k+vE`. Its positive residue gives `v>=0`. If `v>=1`,
then `E>R+5` implies `2n>2R`, contradicting `n<p=R`. Hence
`2n=R+epsilon_k`. If `epsilon_k=-1`, then `p=2n+1`; the Pell duplication
identity and monotonicity force `c>k(Y+1)`, contrary to
`c=kY+eta<k(Y+1)`. Therefore `Nk=1` and `R=2n-1` is odd.

This application does not invoke the conclusion of the parent universal
polynomial theorem. In particular it does not first pretend to restore a
parent zero while some unit signs remain unknown.

## 4. Dyadic recovery before the repunit sign

Write `R=2r+1`, where `r=n-1>=1`. The lower Pell-ratio estimate from
`complete75_asymmetric_scale_tradeoffs.md`, Section 3, uses only the two
Pell equations, the supplied ratio interval, `X>=16`, `Y>=4096`, and
`6XY^2>a`. All those conditions hold here. It gives

```
c/(k/2) > (X+1)^(2r)/X^r > X^r,
Y > X^r/3,
a > X^(r+1)/3 > 2^(2r+1) = 2^R.
```

The main-root projection satisfies
`chi_A(R)-a*psi_A(R)=2^R (mod 4a+3)`. By the literal definition of `D`,
its left side equals `X+gamma*(4a+3)`. Since both `X` and `2^R` are
positive and below `a`, they are equal: `X=2^R`.

This is the step at which using an exact repunit prematurely would create a
circular proof. The lower-ratio argument above needs no repunit identity,
no input norm, and no population decoding. Since `q^2` divides `X`, it now
follows that `q=2^u` for an integer `u>0`.

If `epsilon=-1`, the equation `q-beta*J=-1` would say
`2^u=-1 (mod 2^d-1)`. Reducing `u` modulo `d` yields a remainder `v<d`,
but for `d>=3`,

`0<2^v+1<=2^(d-1)+1<2^d-1`.

This is impossible. Therefore `Ne=1`; now and only now,
`e=q-1`, `J=(q-1)/(B-1)`, and `q=B^N` for some positive integer `N`.
The product of units then forces `Nt=1` as well.

## 5. Return to the native compiler

After `e=q-1`, the packed index becomes the exact inherited source

`R=(q^2-Z-qF)*(q^2-1)+(MC+q*MF)*J`.

The lower bound on `R` gives `R>3q>3u`. Hence `q^3` divides `X=2^R`
and `w_old=X/q^3=w/q` is a positive integer. The required symmetric
scale `X=w_old*q^3` is therefore restored.

The transport equation `Nt=1` is

`(K+w)C=F+(t-1)(q-1)`.

The positive integer

`z=t-1+w(q+1)C`

satisfies the physical transport equation

`(K+X)C=F+z(q-1)`.

The auxiliary coordinates in Section 3 restore the remaining positive
native witnesses. The input specialization is literal: `C-Z=W0=2^b*B^2`.
The inherited modified75 population, type, synchronization, and dummy-control
proofs now apply with their actual masks. `W0<C<q=B^N` gives `N>2`, so the
unique End selector is at cyclic cell 2, without wrapping. The shifted low
mask inserts Start at cell 0; the cyclic marker bijection makes it unique.
The resulting initial row has an I-run of length three, including four unary
ones when Q is counted.

For completeness, a genuine halting normalized tableau supplies the parent
positive witnesses at ordinary input 1. Keep its values of `X,Y,R,c,a` and
set `w_new=X/q^2`, a positive integer by the preceding dyadic divisibility
property of parent zeros. Its new transport quotient is defined by

`t_new-1=((K+w_new)C-F)/(q-1)`.

Integrality follows from `X=w_new*q^2`, hence `X=w_new (mod q-1)` and
the parent transport congruence. Positivity follows already because its
integer quotient is greater than -1: `C,K,w_new>0` and `F<q`.
The new slack is `alpha_new=q-C-F=Z+alpha_old+2d>0`, and the main-root
coordinate is `gamma=rho+sigma>0`. The positive auxiliary quotient is the
retained Bezout projection `(o+R*f)/c`. Every seven-unit equation then holds.
Thus the construction preserves existence in both directions, without
assuming a fresh canonical choice for the parent's other witnesses.

## 6. Exact operation and degree audit

The JSON has 70 arithmetic rows and no dead row or supplied port. Fixed
numerals are inputs under the repository's operation convention. This count
does not measure their bit length or the effort required to expand them.

The exact degrees of the seven displayed, scaled factors are

`24,20,1,64,8,2,50`.

Their sum is 169. The main norm has a leading cancellation; a naive degree
propagation through the source returns 173 for the final polynomial and is
only an upper bound.

A uniform leading-term proof avoids reliance on finite specialization tests.
Put `Q=Z+F+alpha` and `k0=eta+zeta`, the highest homogeneous parts of q and k.
Then `a_top=w*s*Q^5` and `c_top=k0*s*Q^3`. The factor leaders are

```
N0:        -w^2*s^4*k0^2*Q^16,
Nm:         8*gamma*k0*w^2*s^3*Q^13,
Ne:         Q-beta*J,
Na:         i^2*k0^6*w^4*s^10*Q^38*T^2*f^2,
Nk:        -h*w*s*Q^5,
Nt:         w*Z-beta*t*J,
Ns_scaled: -i^2*k0^4*w^4*s^8*Q^32.
```

Their product is

```
-8*h*gamma*i^4*k0^13*w^13*s^26*T^2*f^2*Q^104
    *(Q-beta*J)*(w*Z-beta*t*J).
```

It is nonzero for every admissible fixed coefficient instance. Subtracting
`Delta`, of degree 14, cannot change it. Thus 169 is the exact total degree.

## 7. Literal machine, finite windows, and constants

The independent verifier authenticates the released 430-row K215 table and
checks the emitted 4,350-row normalized table at all 5,160 combinations of
original state, side, pair contents, and representative physical positions
0, -1, -3. It computes expected motion from virtual tape coordinates rather
than importing the normalizer's fold routine. It also directly executes the
distinguished four-one loader, obtaining blank folded K215 after ten steps.

The induction in `NORMALIZATION.md` establishes global equivalence; local
finite checks are supporting evidence. Trap and halt are absorbing, and no
valid simulation reaches halt except through a corresponding K215 halt.

The tile predicate was reviewed clause by clause: phase initialization,
vertical and horizontal boundary propagation, unique incoming heads, no
head escape through a vertical boundary, final-row halting, and the exact
stationary first-step marker. The cyclic marker argument is recorded in
`FIXED_INPUT_SEMANTICS_REVIEW.md`. In particular it works on cyclic indices
without assuming that the helical stride divides the period. Unique End
forces unique Start, and the interval between nearest vertical boundaries
and successive horizontal boundaries is a genuine accepting computation.

The compressed window census is an exact partition of the five-cell
predicate, with four independent free corners. Its values are

```
tile count = 4366,
accepted crosses = 311471256024587,
window count = 113175624520853754856480928432.
```

The formulas in `COEFFICIENTS.md` were compared with the pinned source
`explore_fixed_raw_universal_76.py::compile_windows` and
`complete75_half_binomial_compiler.py::{compile_windows,new_constants}`.
The payload ordering, selector coefficients, padding clauses, one dummy,
four anchors, two clause bands, optional high monomial, and two modified
masks agree. In particular the source mask is `MF_native+B-1`, not the
native mask itself.

For the compact radix calculation, if `S` is the sum of native coefficients,
then `S <= (14k+9a+4) A^(9a+4)`. The explicit bit-length margin in
`compact_layout` puts `4(m+3)(2S+6)+8` strictly below the leading padded
term of `2mu+4`. The latter's target bit length is
`ell*(9a+4+padding)+2`. Thus the least allowed powers are exactly
`b=5^44`, `L=5^45`, and `d=5^89` as stated. No giant integer or full window
list was expanded in this review.

## 8. ZFC calibration and the scope of the result

The exact inherited endpoint is

`BlankHalts(machine215) <-> BProv ZFCax_s [] Form.fBot`.

The source pins and theorem paths are in `FIXED_INPUT_SEMANTICS_REVIEW.md`.
Its proof enumerates finite refutations, with the ZF-to-ZFC calibration
provided by the constructible-model equiconsistency argument. The definition
of consistency here is absence of a finite syntactic refutation, not existence
of a well-founded or transitive model and not an assumption that ZFC is true.

The finite table transformation, cyclic computation coding, integer/Pell
arguments, and finite proof-system calibration are ordinary mathematics
formalizable in ZFC. The claim of provability in ZFC uses these arguments;
one must not infer internal ZFC provability merely from the fact that an
external proof assistant checked a theorem. The K215 endpoint README itself
explicitly separates those notions. This packet does not contain a newly
encoded derivation in ZFC's own syntax and does not freshly rebuild the Lean
or Rocq endpoint.

Combining the reviewed equivalences gives, in ZFC,

`exists positive witnesses, P=0 <-> exists finite ZFC refutation`.

Negating this statement yields the requested equivalence with `Con(ZFC)`.
It does not prove either consistency or nonexistence of witnesses. Converting
strictly positive witnesses to natural-number or unrestricted-integer domains
requires the explicit standard substitutions stated in the main report.
