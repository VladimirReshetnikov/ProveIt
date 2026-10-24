# Centered fixed-blank root elimination

This directory gives ordinary mathematical reductions on the **whole compact36 tuple**, preserving the fourteen strictly positive supplied coordinates

```
J,F,alpha,z,h,i,T,s,w,tau,eta,zeta,y,gamma.
```

The letters f and the old auxiliary ordinate are reconstructed, not additional unknowns. [field74.json](field74.json) has 74 live binary operations and exact degree 312. [ordinary76.json](ordinary76.json) has 76 operations and exact degree 191. The normalized [unit76_reference.json](unit76_reference.json), 76/263, is retained as a transparent intermediate and is dominated by the ordinary version. No Lean work was performed; formalization is paused. The proofs compose with the explicitly inherited ordinary compiler/refutation calibration and do not certify it anew internally.

## Fixed source, coefficients, and common abbreviations

The pinned inert parent is [compact36 P67](../../con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json), SHA256 `732fecec5df8fecf98019f9aeadab7a63579c3ebfe6c179cbd7027dee24e9d08`. The four fixed integer ports are exactly its `beta,K0,MC,MF_source`; all four raw/gzip payloads are authenticated in [BUILD.json](BUILD.json). In particular `beta=2^1012115-1`. The source binding must not be mixed with compact44 or source31.

Use the parent's unchanged first, main, index and old-z transport factors:

```
q=beta J+1, C=q-F-alpha, X=wq, Y=sq³, E=XY,
k=eta+zeta, c=kY+eta, a=E+Y, A0=a+2,
H=4a+3, Delta=A0²-1=a²+H,
Dmain=X+ac+gamma H, ell=EkY,
R=[(q-1)(q-F)+alpha](q²-1)+(MC+q MF_source)J,
N0=tau²-ell(ell+k), N1=Dmain²-Delta c²,
Nk=k-hE-R, Nt=(K0+w)C+(q-F)-z(q-1),
P=N0 N1 Nk Nt, u=cT.
```

The actual tuple has `B=2^d,d>=4,beta=B-1,K0>0`, native masks `0<MC,MF_native<B-1`, `MC=2 mod4`, `MF_native=4 mod8`, population sum d, and `MF_source=MF_native+B-1`. The payload and ordinary whole-tuple compiler interface are proved in [compact36 coefficients/PROOF.md](../../con-zfc-diophantine-forms/36-small-tuple/coefficients/PROOF.md), notably Sections 4, 6 and 7. Section 7 expressly licenses compatible ordinary arithmetic skeletons; it is not a claim that every normalized old zero admits division of its i coordinate by Delta.

## A. One-operation auxiliary centering in the normalized root deletion

Let `I=i c²`, `D=1+Delta I²`, `Q=Delta²I²`, `b=c+RD`. The old auxiliary expression is

```
V=u f-c-Rf²,
Na=QV²-(Q-1)y_old².
```

Replace the supplied ordinate by `y=y_old+b`, so proof-only `y_old=y-b`. Put

```
A=Q(Du²+b²)-(Q-1)(y-b)²-1,
B1=2Qub, K=A²-D B1².

F74=[P(A+1)-1]²-D(P B1)²,
F76_reference=P(K+1)-1.
```

These are the complete tail formulas. The literal evaluator uses the equal identity `A=Q[Du²+b²-(y-b)²]+(y-b)²-1` to share its ordinate square. Compared with the earlier 73/342 and 75/293 candidates, it adds just the subtraction `y-b` and relocates the existing auxiliary square after b is available.

The [previous root-elimination proof](../fixed-root-elimination/PROOF.md) applies with a signed y_old because every occurrence of that ordinate is squared. Its nonvanishing follows at a restored auxiliary unit: `y_old=0` would force the integer square Q times V² equal to one, whereas Q>1. Taking its absolute value restores a strictly positive source ordinate.

For completeness, that proof's algebra has `B1!=0` before any source equation: D>c, hence `b=c+RD` is nonzero for every integer R. At a field zero P is nonzero and the rational extracted root squares to the positive integer D, so is a nonzero integer. Substitution gives `P Na=1`; Q square excludes Na=-1 modulo four, so P=Na=1. At a unit zero, `K+1` cannot equal -1 modulo four because B1 is even, giving P=1 and K=0. The same unique integer root follows. Strong-root sign is restored by the fixed-blank signed-T theorem: f and T occur only through f² and Tf; a negative f at supplied T>0 would yield a positive-f, negative-T source zero, which the theorem excludes.

Every canonical positive parent solution has R>0, hence b>0. Thus `y=y_old+b>0`, proving reverse existence. No bijection between all positive new and old ordinate coordinates is asserted: the soundness map may take an absolute value.

The leading Qb² term cancels against the shifted ordinate term. With the actual parent degrees `deg(Q,D,b,u,P)=(46,34,38,6,49)`, A has degree 92 instead of 122. The field output is dominated by `-D(P B1)²`, degree 312; the unit output is dominated by `-P D B1²`, degree 263.

## B. Ordinary strong norm and scaled auxiliary centering

The ordinary variant uses the same supplied positive i, now through

```
I=i c², Q=I², Dnum=Delta+Q,
bnum=Delta c+R Dnum,
p=Delta Dnum u²,
y_old=(y-bnum)/Delta.
```

Only y_old is rational at the beginning of the inverse proof. Define the integer polynomials

```
A=Q(p+bnum²)-(Q-1)(y-bnum)²-Delta²,
B1=2Qubnum,
K=A²-Delta Dnum B1² = A²-4Q² p bnum²,
F76=P(K+1)-1.
```

The literal computes p as `Ac2*Dnum*T²`, where `Ac2=Delta c²` already belongs to the main source. It deletes the now-unused normalized coefficient pair `i*Ac2,(i*Ac2)²`, and computes I,Q in its place. These two sharing choices bring the total down to 76 operations. All names remain polynomial abbreviations; no division occurs in the actual equation.

### B1. Expose the first/main equations before extracting f

Since the subtracted term of K has an explicit factor four, `K+1` is 1 or 2 modulo four and cannot be -1. Integer `P(K+1)=1` therefore forces **P=1,K=0**. Hence each of N0,N1,Nk,Nt is an integer unit. The consecutive-product negative-Pell theorem excludes N0=-1 because its coefficient `XY²>1`. Since `Delta=A0²-1` is 0 or 3 modulo four, N1=-1 is also impossible. Thus

```
N0=N1=1, Nk=epsilon, Nt=nu, epsilon,nu in {+1,-1}, epsilon*nu=1.
```

The weak transport argument permits the genuine `C=0,F=2,z=1,nu=-1` boundary; it must not be excluded prematurely. On the actual masks it nevertheless gives

```
q>=16, R-2>3q+1, 0<R<q⁴-2, E>=q⁴>R+2, a>R+2.
```

These are exactly the early fixed-blank inequalities used in [the previous signed-T proof](../fixed-root-elimination/PROOF.md), Steps 2–3, before using any strong or auxiliary root.

First/main Pell classification gives positive n,p with

```
tau=chi_(2XY²+1)(n), k=2psi_(2XY²+1)(n),
Dmain=chi_A0(p), c=psi_A0(p).
```

The index equation modulo E gives `2n=R+epsilon+vE`. Since `0<R+epsilon<E`, v is nonnegative, and `n>=(R-1)/2>=24`. Monotonicity, `2XY²+1>A0` and `c>k` give p>n. In particular p>=6. The exact identity

```
psi_A0(6)-A0(A0²-1)²=A0(31A0⁴-30A0²+5)>0
```

now supplies **c>A0 Delta²**, without assuming that f exists, is integral, or has any strong rank. Also c>2p, and the literal index equation gives k>R, hence c>2R.

### B2. Rational ordinary-root integrality by balanced unit reduction

The following elementary lemma is the missing step in a naive ordinary-root transfer.

**Lemma.** Let A>=2 and p>=1 be integers, `Delta=A²-1`, `c=psi_A(p)>A Delta²`, and I a positive integer divisible by c. If f is rational and `Delta(f²-1)=I²`, then f is a nonzero integer. More precisely, for some positive multiple m of p,

```
|f|=chi_A(m), I=Delta psi_A(m).
```

**Proof.** Put `g=Delta|f|`. Its square is the integer `Delta²+Delta I²`, so rational-square integrality gives g an integer. Let `e=A+sqrt(Delta)>1` and `alpha=g+I sqrt(Delta)>Delta`. Both alpha and e lie in `Z[sqrt(Delta)]`, and their norms are Delta² and one.

Choose an integer j so that

```
Delta*e^(-p/2) <= alpha*e^(-jp) < Delta*e^(p/2).
```

This is an ordinary real Archimedean choice of a representative in one multiplicative interval of ratio e^p. Set `alpha0=x0+y0 sqrt(Delta)`. Both x0,y0 are integers, since `e^(-1)=A-sqrt(Delta)`. The ordinate y0 is divisible by c: every integer power of e^p has its square-root coefficient divisible by `psi_A(p)=c`, and multiplication preserves this divisibility when c|I.

The conjugate of alpha0 is `Delta²/alpha0`. The interval therefore gives

```
|y0| <= Delta*(e^(p/2)-e^(-p/2))/(2sqrt(Delta))
      = Delta*c/(e^(p/2)+e^(-p/2)) < c.
```

The last inequality follows because `(e^(p/2)+e^(-p/2))²=2chi_A(p)+2`, while `chi_A(p)>c>A Delta²`, so the denominator is greater than Delta. Hence the integer y0 divisible by c is zero. The positive norm then makes alpha0=Delta. Thus `alpha=Delta e^(jp)`. Since alpha>Delta, j>0; comparing coefficients proves the lemma with m=jp. This does not require a parser, an internal transfer principle, or classification of arbitrary rational Pell points. ∎

The size hypothesis is essential to the inference used here: for A=8, Delta=63, I=7, f=4/3 the ordinary equation holds but f is not integral. This exact negative control is checked. It is not a zero of the whole source, whose early main bound excludes that small c.

### B3. Extract the actual root and the old auxiliary ordinate

After B1, R>0, so bnum>0. Also Q,u>0, giving B1!=0. From K=0 the rational

```
g=A/B1, f=g/Delta
```

satisfies `g²=Delta Dnum` and `Delta(f²-1)=Q=I²`. The preceding lemma, already licensed by B1's c bound and c|I, makes f a nonzero integer (of either sign).

The exact universal remainder identity is useful for tracking both denominators. With

```
Estrong=Delta f²-Delta-Q,
V=u f-c-Rf²,
```

one has

```
Delta²[QV²-(Q-1)y_old²-1]
 = A-B1*Delta*f
   + Q*Estrong[Delta u²-2R(Delta u f-bnum)+R² Estrong].
```

Our selected g makes the first line vanish and Estrong=0. Thus `QV²-(Q-1)y_old²=1`. Now Q>1 and V is integral. The adjacent-coefficient rational Pell descent makes y_old an integer. It is nonzero, as otherwise the integer square Q>1 times V² would equal one. Take its absolute value as the positive old source ordinate. Notice the order: neither f nor y_old was assumed integral merely because the cleared resultant vanished.

### B4. Universal fixed-blank signed-root reconstruction for the ordinary norm

It remains to justify that the recovered root is positive, without assuming the positive source before proving positivity. Repeat the ten-step [fixed-blank signed-T proof](../fixed-root-elimination/PROOF.md), with its Step 4 replaced by the following ordinary argument.

The lemma gives `|f|=chi_A0(m)`, p|m, and `I=Delta psi_A0(m)`. Write m=pv. Since `c²|I`, composition yields `c|Delta psi_Dmain(v)`. The congruence `psi_Dmain(v)=v Dmain^(v-1) mod c` and `gcd(Dmain,c)=1` give `c|Delta v`. Also

```
gcd(c,Delta)=gcd(p,Delta) divides p,
```

by `psi_A0(p)=p A0^(p-1) mod Delta`. Hence c|pv=m. Consequently `m>=c>2p`. Moreover `f²-1=Delta psi_A0(m)²` is divisible by c², and `|f|>c²/sqrt(Delta)>2c`.

These are precisely the strong conclusions needed later; the normalized conclusion pc|m is unnecessary. Put S=I, so `S²=Delta(f²-1)=Q`, and c|S. The literal auxiliary congruences are still `V=-c mod f` and `V=-R mod c`. Also `S²=-Delta mod f` and `S²=0 mod c`. Thus the same odd Chebyshev quotient, signed step-down and strict intervals give **p=R**, without any assumption on the sign of T or V. The ± index/transport signs then become +1 by the same duplication contradiction, so C>0 and R=2n-1 is odd.

For clarity, the remaining parity step is the actual fixed-blank one, not an imported input equation. The unchanged lower/main-root ratio yields `X=2^R`, `q=2^t=B^N`, and the parity-free half-binomial valuation yields `popcount(R)>=3t+2`. With the exact shifted masks put

```
Sword=(C-1)+qF,
Tword=(MC J+1)+q(MF_native J-1).
```

The exact rank identity `R=(q²-Sword)(q²-1)+Tword`, the authentic population `popcount(Tword)=t+2`, and the inverse-population lemma force `Sword AND Tword=0`. Its two lowest bits give C=1 modulo four, hence **R=3 modulo four**. None of this uses the deleted input norm. These unchanged ratio/population proofs and their source pins are given explicitly in the prior proof's Steps 7–9.

Finally the two unsquared auxiliary congruences, with `ell_aux=±R+2m z0`, force z0 even and `sign(V)*(-1)^((R-1)/2)=-1`. Since R=3 modulo four, V>0. Thus `c T f=V+c+R f²>0`. This argument applies to positive |f| with any signed T, and proves T>0. If the uniquely extracted f were negative at our supplied T>0, replacing f,T by -f,-T preserves V and all other source equations, contradicting that result. Therefore the extracted f is positive.

We have reconstructed the ordinary positive strong/auxiliary source with every other original coordinate positive, except that the old auxiliary y was replaced by its absolute value. The ordinary product strong factor is `1+I²-Delta(f²-1)=1`; all the other factors are one as proved. This is exactly the old-z product interface in [ordinary_blank_proof.md](../../con-zfc-diophantine-forms/36-small-tuple/positive/upstream/ordinary_blank_proof.md), Section 1, with the compatible whole compact36 tuple licensed by its coefficient proof. Its ordinary native/compiler calibration supplies the same finite refutation endpoint. No division of arbitrary supplied i by Delta is asserted.

### B5. Canonical completeness

Conversely, a finite refutation supplies canonical normalized compact36 P67 witnesses. Retain f,T and every source coordinate except the two encoded ones. Set

```
i_ordinary=Delta*i_normalized,
I=i_ordinary c², Q=I²,
Dnum=Delta+Q=Delta f²,
bnum=Delta c+R Dnum,
y_new=Delta*y_old+bnum.
```

These are strictly positive integers because R>0 and the old ordinate is positive. The authentic auxiliary coefficient Q is unchanged. Estrong=0 and Na=1 make `A=B1*Delta*f` by the universal identity; since `(Delta*f)²=Delta Dnum`, K=0. The unchanged four-factor P is one, so F76=0. This proves reverse existence through canonical witnesses, not a pointwise inverse division of arbitrary i.

## C. Exact circuit and degree evidence

The builders import no archived H10 emitter and evaluate no frozen power array. They read the pinned P67 as inert JSON and reuse only elementary helpers from our earlier root-elimination builder. `check.py` imports no construction builder: it independently checks the retained prefix, topology/liveness, complete literal tail identities, the full ordinary remainder, integer norm preservation, main norm cancellation, and degree leaders. Its tiny sparse-ring utility is credited/pinned in the receipt.

All actual coefficient bytes are checked against the unchanged compact36 binding. Normal and optimized checks pass. The complete fourteen-variable polynomials remain compact ordered circuits rather than exponentially expanded coefficient lists.

Write `q0=beta J`, `k0=eta+zeta`, and `Nt0=w(q0-F-alpha)-zq0`. The prefix leader is

```
P0=8h gamma k0³ w⁵ s⁸ q0^29 Nt0,
Delta0=w²s²q0⁸, c0=k0 s q0³, R0=q0³(q0-F).
```

The ordinary coefficient `Q0=i²k0⁴s⁴q0^12` has degree 22, Dnum degree 22, bnum degree 26, and p degree 46. A's degree-68 leader is Q0*p0, while the uniquely larger cross term gives `K_top=-4Q0² p0 bnum0²`, degree 142. Multiplication by P0 gives exact degree 191. Uniform nonzero coefficients after actual numerical specialization are:

| Literal | Selected monomial | Coefficient |
|---|---|---|
| field74, degree312 | `J^188 h² gamma² i^10 eta^28 w^24 s^52 T² F² z²` | `-256 beta^188` |
| unit76 reference, degree263 | `J^158 h gamma i^10 eta^25 w^19 s^44 T² F² z` | `32 beta^158` |
| ordinary76, degree191 | `J^110 h gamma i^10 eta^25 w^7 s^32 T² F² z` | `32 beta^110` |

All are independent of K0,MC,MF, so the degree cannot disappear upon specializing the actual tuple. field74 uses 44 multiplications and 30 additions/subtractions; both unit circuits use 44 and 32. Every row, unknown and port is live.

## D. Scope and genuine failed shortcut

The uncentered ordinary norm would require clearing Delta² in its auxiliary expression. Without the ordinate center it costs 79 operations at degree197 after sharing the existing Ac2; it is not a useful degree/cost improvement over existing 79/52 forms. The scaled coordinate `y_new=Delta*y_old+bnum` is what removes those extra scales and cancels its leading auxiliary term.

A direct field-style ordinary resultant has no supplied proof here: unlike the unit finalizer, it does not first force the first/main factors to be units. Using the large-c integrality lemma before obtaining that bound would be circular. The 4/3 counterexample shows why one cannot simply substitute the rational ordinary radicand into the old integer-root proof. No such unverified field polynomial is promoted as a consistency equation.

The old 73/342 and75/293 candidates remain useful operation-count tradeoffs. The new74/312 and76/191 points are ordinary fixed-blank improvements, not a global optimum claim. This directory preserves compact36's whole coefficient tuple; other14-positive degree/cost frontiers on other tuples remain separate comparisons. Native semantic calibration, internal nonstandard-code transport and end-to-end Lean verification retain their previously stated boundaries.
