# Fourteen positive variables by deleting the strong root

The literal circuits`field73.json` and`unit75.json` have respectively
73 binary operations/exact degree342 and75/exact degree293, with fourteen
strictly positive unknowns. They retain all variables of package36's P67
except`f`, and its **whole four-integer tuple**. Their ordinary proof is
below. The [independent mathematical review](INDEPENDENT_REVIEW.md) passes.
No new Lean or internal
object-ZFC certificate is claimed; all Lean work remains paused.

## Exact source and port contract

The parent is `36-small-tuple/baseline/product67.json`, SHA256
`732fecec5df8fecf98019f9aeadab7a63579c3ebfe6c179cbd7027dee24e9d08`.
The new supplied list is

```text
J,F,alpha,z,h,i,T,s,w,tau,eta,zeta,y,gamma >0.
```

Use the unchanged parent abbreviations

```text
q=beta*J+1, C=q-F-alpha, X=w*q, Y=s*q³, E=X*Y,
k=eta+zeta, c=k*Y+eta, a=E+Y, A0=a+2,
H=4a+3, Delta=A0²-1, Dmain=X+a*c+gamma*H,
R=[(q-1)(q-F)+alpha]*(q²-1)+(MC+q*MF_source)*J.
```

The arithmetic port hypotheses are

```text
B=2^d, d>=4, beta=B-1, K0>0,
0<MC,MF_native<B-1,
MC≡2(mod4), MF_native≡4(mod8),
popcount(MC)+popcount(MF_native)=d,
MF_source=MF_native+B-1.
```

They are proved for the actual materialized package36 tuple in its
`coefficients/PROOF.md`, Sections4 and6, and checked again on the actual
payloads by`build.py`. Native/compiler soundness and completeness use the
entire package36 coefficient recipe, not merely these arithmetic hypotheses.

Let`N0,N1,Na,Nk,Nt` denote the parent's first, main, auxiliary, index and
transport factors. Put

```text
S=Delta*i*c², Q=S²,
V=c*(T*f-1)-R*f²,
Na=Q*V²-(Q-1)*y²,
Ns=f²-Delta*(i*c²)²,
P=N0*N1*Nk*Nt.
```

The parent equation is identically`Delta*(P*Na*Ns-1)=0`.
Before any equation,`Delta>0` because the remaining supplied variables are
positive. All statements in the next section allow **T to be any integer**,
while retaining`f>0` and all other parent coordinates positive.

## Fixed-blank signed-T positivity, with dependency order

**Claim.** Every such parent zero has`T>0` on the stated arithmetic port
contract. The deleted input norm is not needed.

1. Cancel`Delta`. Each normalized factor is an integer unit. The inherited
   consecutive-product negative-Pell lemma excludes`N0=-1`; its coefficient
   parameter`XY²>1`, so the exceptional parameter1 is absent. Square residues
   modulo4 exclude`N1=-1,Ns=-1`; the fact`Q` is a square excludes`Na=-1`.
   Hence`N0=N1=Na=Ns=1`, while`Nk=epsilon,Nt=nu`, with
   `epsilon,nu∈{±1}` and`epsilon*nu=1`.

2. The weak transport bound gives`C>=0` and permits the genuine boundary
   `C=0,F=2,z=1,alpha=q-2,nu=-1`. Retain it. Exactly as in package36's
   `FIXED_BLANK_67_PROOF.md`, Section2,

   ```text
   q>=B>=16, R-2>3q+1, 0<R<q⁴-2,
   E>=q⁴>R+2, a>R+2, k*Y<c<k*(Y+1).
   ```

   In particular no argument requiring the older margin`R<q⁴-q³` is used.

3. Write`chi_A,psi_A` for the standard Pell sequences with discriminant
   `A²-1`, and put`P0=2XY²+1`. Positive-root classification of`N0=N1=1`
   gives`tau=chi_P0(n), k=2psi_P0(n)` and
   `Dmain=chi_A0(p), c=psi_A0(p)`. Reduction modulo`E` gives
   `2n=R+epsilon+vE`, with`v>=0`, so`n>=(R-1)/2>=24`.
   Since`P0>A0` and`c>k`, monotonicity gives`p>n` and`c>2p`.
   The literal index equation with`h>=1` gives`k>R`, hence`c>2R`.

4. The strong equation classifies
   `f=chi_A0(m), psi_A0(m)=i*c²`. Thus`p|m`. Write`m=p*b`.
   Expanding the square-root coefficient of
   `(chi_A0(p)+c*sqrt(Delta))^b` and dividing by`c` gives, modulo`c`,
   `psi_A0(m)/c=b*chi_A0(p)^(b-1)`. Its left side is divisible by`c`,
   and`gcd(chi_A0(p),c)=1`; hence`c|b`. Therefore`pc|m`, so`m>2p`
   and`c|m`. Directly from the strong equation,`f>c²>2c`.
   This normalized-rank proof uses no sign of`T,V` and no input norm.

5. The auxiliary norm gives`V!=0`. Let`e=sign(V)` and classify the positive
   absolute-root solution:
   `S*|V|=chi_S(ell), y=psi_S(ell)`. Divisibility by`S` makes
   `ell=2v0+1` odd. The odd Chebyshev quotient satisfies

   ```text
   V=e*C_v0(S²),
   C_v0(1-A0²)=(-1)^v0*psi_A0(ell),
   C_v0(0)=(-1)^v0*ell.
   ```

   The **literal** source gives`V≡-c(mod f)` and`V≡-R(mod c)`.
   Also`S²≡-Delta(mod f)` and`S²≡0(mod c)`. Squaring the first
   congruence gives`chi_A0(2ell)≡chi_A0(2p)(mod chi_A0(m))`.
   The plus-sign step-down lemma, with`0<2p<m`, gives
   `ell≡±p(mod2m)`. Since`c|m`, the second unsquared congruence then
   gives`R≡±p(mod c)`. The strict bounds`0<R,p<c/2` force`p=R`.
   These are precisely the signed local steps in package36's
   `SIGNED_DOMAIN_29.md`, without any need for its completeness restrictions
   of odd`i` or square`w`: here`i,w>0` already supply all sign hypotheses.

6. Now`n<p=R` and`E>R+2` force`v=0`. If`epsilon=-1`, then
   `p=2n+1`; Pell duplication,`chi_A0(2)>P0` and`A0>Y+1` imply
   `c>k*(Y+1)`, a contradiction. Thus`epsilon=nu=1`,
   `R=2n-1` is odd, and the transport factor now gives`C>0`.

7. Put`r=(R-1)/2>=24`, so`n=r+1`. The elementary estimates
   `(2L-1)^(j-1)<=psi_L(j)<=(2L)^(j-1)` give, with
   `xi=(X+1)^(2r)/X^r`,

   ```text
   c/(k/2)>xi,
   Y>xi/2-1>X^r/3,
   a>X^(r+1)/3,
   0<2^R<a and 0<X<a.
   ```

   The strict first comparison uses`6XY²>a`; it needs no parity of`r`.
   The Pell recurrence gives`chi_A0(R)-a*psi_A0(R)≡2^R(mod H)`.
   The main source gives the same expression`X+gamma*H`. Both positive
   representatives are below`a<H`, hence`X=2^R`.
   Since`q|X`, write`q=2^t`; the repunit equation implies`d|t`,
   `q=B^N`, `t=dN`, with`N>=1`.

8. The complementary upper ratio gives
   `0<c/k-xi/2<16r/(X+1)<1/2`. Expand

   ```text
   xi=M+theta,
   M=binom(2r,r)+sum_(j=1)^r binom(2r,r+j)*X^j,
   0<theta<1/4.
   ```

   `M` is even, so the strict interval`Y<c/k<Y+1` forces`Y=M/2`.
   The other terms are divisible by`2^R`, while
   `v2(binom(2r,r))=popcount(r)<R`. Consequently
   `v2(Y)=popcount(r)-1`. As`q³|Y`,
   `popcount(R)=popcount(r)+1>=3t+2`.
   This is the parity-free half-binomial argument in the signed-T source
   proof, Sections2–3; no accepting history or input index has been assumed.

9. **Actual fixed-blank mask binding.** Substitute`C` for the universal
   proof's separate`Z`. Define

   ```text
   Sword=(C-1)+q*F,
   Tlow=MC*J+1, Thigh=MF_native*J-1,
   Tword=Tlow+q*Thigh.
   ```

   Direct expansion of the actual P67 rank gives
   `R=(q²-Sword)*(q²-1)+Tword`. Because`F,C>0` and`F+C=q-alpha<q`,
   `1<=Sword<q²`. The valid mask bounds and`q=B^N` give
   `0<Tword<q²-1` and`popcount(Tword)=t+2`: the low increment and high
   decrement each add one bit, using the exact trailing-zero residues.
   The inverse-population lemma now bounds`popcount(R)<=3t+2`, with equality
   exactly when`Sword AND Tword=0`. The threshold in step8 forces equality.
   Thus`(C-1) AND(MC*J+1)=0`. Since`J≡1(mod4)` and`MC≡2(mod4)`,
   `C≡1(mod4)`. The literal rank modulo4 is`R≡C+MC*J`, so
   **R≡3(mod4)**. This step uses the actual shifted mask and does not use
   any deleted input equation or a powers-of-five geometry assumption.

10. Return to the two **unsquared** auxiliary congruences. The strong
    step-down in step5 now writes`ell=epsilon0*R+2m*z0`, with
    `epsilon0∈{±1}`. Pell addition modulo`f` gives
    `psi_A0(ell)≡epsilon0*(-1)^z0*c(mod f)`, while
    `ell≡epsilon0*R(mod c)`. Substitution into both congruences yields

    ```text
    e*(-1)^(r+m*z0)*R ≡ -R (mod c),
    e*(-1)^(r+(m+1)*z0)*c ≡ -c (mod f).
    ```

    Because`c>2R,f>2c`, each sign is exactly`-1` as an integer.
    Their quotient forces`z0` even, regardless of`m`'s parity. Thus
    `e*(-1)^r=-1`. Step9 makes`r` odd, giving`e=+1`, hence`V>0`.
    Finally`c*T*f=V+c+R*f²>0`, so **T>0**.

This proves the claim, restoring the same supplied tuple. It is not an
appeal to the positive parent before positivity has been restored.

## Root-elimination algebra and the integer inverse

Use new proof abbreviations

```text
D=1+Delta*i²*c⁴, b=c+R*D, u=c*T,
Arat=Q*(D*u²+b²)-(Q-1)*y²-1, Brat=2*Q*u*b,
Knorm=Arat²-D*Brat².
```

Since`D>c>0`, `b=c+R*D` is positive when`R>=0` and negative when`R<=-1`;
it never vanishes. Thus`Brat!=0` on the entire retained positive domain,
before imposing any native condition. If`Ef=f²-D`, direct expansion gives

```text
Na-1=Arat-Brat*f+Ef*qaux,
qaux=Q*(u²-2R*u*f+2R*b+R²*Ef),
Ns=1+Ef.
```

The first candidate is`F73=[P*(Arat+1)-1]²-D*(P*Brat)²`.
At its zero,`P!=0`; otherwise its value is1. The rational number
`f=[P*(Arat+1)-1]/(P*Brat)` squares to the positive integer`D` and is
therefore a nonzero integer. Substitution gives`P*Na=1`. Square residues
exclude`Na=-1`, so`P=Na=1`, and the restored parent vanishes. This also
gives the unique root`f=Arat/Brat`.

The second is`F75=P*(Knorm+1)-1`. Since`Brat` is even, its integer-unit
factor`Knorm+1≡Arat²+1(mod4)` cannot be`-1`. Hence`P=1,Knorm=0`, and
`f=Arat/Brat` is again a unique nonzero integer square root of`D`; the
same identities restore the parent. Conversely any parent zero with signed
nonzero`f` has`Ns=1`, so`Ef=0`; then`Na=P=1` and both candidates vanish.

To prove the restored root positive, observe that the parent's only direct
`f` consumers are`f²` and`T*f`. If`f<0`, replace`f,T` by`-f,-T`.
Every computed parent value is unchanged, yielding a positive-`f`,
negative-`T` zero, contrary to the signed-T theorem above. Thus`f>0`.
Deletion and restoration are inverse bijections of the complete positive
zero sets, preserving every retained witness and all four fixed integers.
The two new polynomials consequently have exactly the same fourteen-variable
positive zero tuples.

Composing with package36's ordinary positive P67/native blank-K215 theorem
gives a ZFC-provable equivalence between existence of a zero and existence
of a sealed finite ZFC refutation. Negation gives unsolvability iff Con(ZFC).
The K215/native and finite-refutation calibration are inherited dependencies;
no proof of Con(ZFC), new kernel certificate, or global minimality is asserted.

## Whole-circuit count, degree, and reproduction

`build.py` reads P67 as inert data, pins its hash, retains its50 independent
rows and appends the explicit23/25-row tails. All73/75 rows, fourteen unknowns
and four fixed ports are live, with no free powers, divisions or factors.
It imports no archived/frozen emitter. The only cancellation missed by naive
degree propagation is the unchanged main norm:

```text
(X+a*c+g)²-(a²+H)*c²
 =X²+2acX+2gX+2acg+g²-Hc².
```

Its unique highest term`2acg` has degree18. The four other-product factors
have degrees22,18,7,2, so`deg(P)=49`. The remaining exact degrees are
`deg(Q)=46,deg(R)=4,deg(D)=34,deg(b)=38,deg(u)=6`, and
`deg(Arat)=122`, dominated by`Q*R²*D²`.
The first tail is dominated by`[P*Q*R²*D²]²`, of degree342; its cross term
has degree312. The second is dominated by`P*Q²*R⁴*D⁴`, of degree293;
the local norm's cross term has degree214 versus its degree244 square.
The stored degree certificates check nonzero leading coefficients using
the **actual bound four-integer tuple** modulo three primes. This establishes
attainment alongside the polynomial upper bound, without evaluating a huge
expanded polynomial or materializing a hypothetical refutation.

```sh
python build.py
python build.py --check
python -O build.py --check
```

These checks certify literal size/binding and transcription. The unbounded
signed-T, Pell, population and native correctness claims rest on the ordinary
proof above and its identified sources; independent review is separate.
