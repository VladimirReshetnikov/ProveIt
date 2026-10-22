# Inputless ordinary-strong systems and a 32-variable quartic

This note first derives its formulas for the inherited four-port arithmetic interface of `06-blank67`; references below to that package's exact coefficients describe this initial derivation. The accompanying report proves transfer to the new four-site recipe, with the final default binding in `../COEFFICIENT_BINDINGS.json` selecting the package-root recipe `compiler/tshape_constants.json` and its shifted MF mask.

Source revision: `3b201cdea32d2c816f5f3d20734051f25fd3ef14`.
All constants below are **exactly** the four constants of package
`06-blank67`, including its shifted verification mask. Write them as
`beta=B-1`, `K0`, `MC`, `MF`; thus `MF=MF_native+B-1`.
No constants from package02 or package07 are substituted into this compiler.

The combination uses three existing ideas:

* package06's raw-K215, inputless window compiler and first scale `X=wq`;
* package02's ordinary strong equation and its independent rank lemma;
* package07's retained positive auxiliary witnesses `o,j`.

The 32-variable quartic then modifies package08's 34-variable quadratic
lift by using ordinary strong scaling and eliminating its packed-index
register through an auxiliary congruence.

All assertions in this note are mathematical proofs using the imported
compiler/Pell theorems. They are not new Lean or Rocq certificates. The
attached programs check exact polynomial identities, degrees and ledgers;
they do not check those imported theorems or decide whether a solution exists.

## 1. Common polynomials

All free variables in this note range over strictly positive integers.
Let

```
q = beta J + 1,
X = wq,       Y = sq^3,       E = XY,
k = eta+zeta, c = kY+eta,     a = E+Y,
H = 4a+3,     Delta = a^2+H,  D = X+ac+gamma H,
C = q-F-alpha,
G = (q-1)(q-F)+alpha,
R = G(q^2-1)+(MC+q MF)J,
Lfirst = E(kY),
I = ic^2,     A0 = Delta(f^2-1).
```

These are abbreviations, not new unknowns, until the quadratic lift in §6.

## 2. Fifteen unknowns, six equations, degree28 and61 operations

Use the fifteen unknowns

```
J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma.
```

Put `V=c(Tf-1)-Rf^2`. The equations are

```
tau^2 - Lfirst(Lfirst+k) = 1,
D^2 - Delta c^2 = 1,
A0(V^2-y^2)+y^2 = 1,
k-hE-R = 1,
(K0+w)C+(q-F)-z(q-1) = 1,
(ic^2)^2 = A0.
```

The fully paid shared circuit is `ordinary15_system61.json`. It has
34 multiplications and27 additions/subtractions, total61. Its exact
residual degrees, in the displayed order, are

```
22,18,28,7,2,22.
```

The sum of squared residuals has exact degree56 and78 operations
(40 multiplications and38 additions/subtractions). This improves
package06's comparison systems without increasing their variable or
operation counts: the old degree60 system also cost61 operations;
the old degree46 alternative cost62.

### Completeness from package06

A solution of the normalized source has

```
f^2-1 = Delta i_normalized^2 c^4.
```

Retain every original coordinate except set
`i_ordinary=Delta i_normalized`. Then

```
(i_ordinary c^2)^2
 = Delta(f^2-1)
 = (i_normalized Delta c^2)^2.
```

The auxiliary coefficient is unchanged and all six new equations hold.
The map is integral and positive. Its inverse need not be integral, and
no division of arbitrary ordinary strong witnesses by Delta is claimed.

### Soundness: proof order and the raw packing bound

The transport equation with value1 forces `C>0`. Indeed, if `C<=0`,

```
(K0+w)C+(q-F)-z(q-1)
 = (K0+w)C+1-F-(z-1)(q-1) <= 0,
```

which contradicts its value1. Hence `F+C<q` and the exact native masks give

```
2q-1 <= G <= q^2-q-1,
0 < (MC+q MF)J < (1+2q)(q-1),
(2q-1)(q^2-1) < R < q^4-q^3,
q >= B >= 16,
E >= q^4 > R+2,       a > R+2.
```

The first norm gives `k=2 psi_P(n)`, `P=2XY^2+1`, `n>=1`.
Modulo E the index equation gives `2n=R+1 (mod E)`, and
`0<R+1<E` implies `n>=(R+1)/2>=24`.
The main norm gives `D=chi_A(p), c=psi_A(p)`, where `A=a+2`.
Since `P>A` and `c>k`, monotonicity gives `p>n`. Standard Pell growth
then gives `c>A Delta^2` and `c>2p`. Also the index equation gives
`k>R`, so `c=kY+eta>2R`.

Now apply the ordinary strong rank lemma stated in package02's
`PELL_INTERFACE_LEMMAS.md`, with hypotheses

```
c=psi_A(p), c>A Delta^2, (ic^2)^2=Delta(f^2-1).
```

Its conclusion is a positive m with

```
f=chi_A(m), p|m, c|m, ic^2=Delta psi_A(m), m>=c>2p.
```

In particular `c^2 | (f^2-1)`. Independently, the strong equation and
the bootstrap bound give

```
f > c^2/sqrt(Delta) > c^2/A > 2c,
f^2 > Delta+c,
A0-(Rf^2+c) = (Delta-R)f^2-Delta-c > 0.
```

The auxiliary norm reads `A0 V^2-(A0-1)y^2=1`. If `v=|V|>1`, it
forces `v>=2A0-1`: use
`v^2-1=(A0-1)(y^2-v^2)` and `y>=v+1`.
But `V>-Rf^2-c>-A0`, excluding every negative V with `|V|>1`.
The norm excludes `V=0`; the congruence `V=-c (mod f)` with `f>2c>4`
excludes `V=+1` and `V=-1`. Thus `V>1`.

Restore positive integers

```
o = cT-Rf,
j = Tf-1-R(f^2-1)/c.
```

Integrality of j uses the preceding rank lemma. The identities
`of=V+c` and `jc=V+R` prove positivity. Consequently

```
V=of-c=jc-R.
```

The signed auxiliary step-down lemma of package02's interface now has
every hypothesis: `I=ic^2>1`, `c|I`, `c|m`, `0<2p<m`, `0<p,R<c/2`,
the two positive minus congruences, and `I^2=Delta(f^2-1)`.
It gives `p=R`.

Writing `2n=R+1+vE` with `v>=0`, any `v>=1` contradicts `n<p=R`
because `E>R+2`. Hence `2n=R+1`. All remaining steps of package06's
inputless arithmetic proof now apply without alteration: the lower
Pell-ratio estimate and main-root congruence give `X=2^R`; since `q|X`,
q is dyadic, and `R>3q` restores `q^3|X`. The half-binomial kernel,
population inversion, repunit order, transport restoration and native
blank-tableau theorem recover a blank halting K215 computation.

Thus the new system is solvable exactly when K215 halts blank. Its
nonexistence is equivalent in ZFC to Con(ZFC), with exactly the same
calibration and formalizability qualifications as package06.

## 3. Optional69-operation polynomial of degree99

Define factors N0,N1,Na,Nk,Nt by the five left sides in §2 and

```
Ns = 1+(ic^2)^2-A0.
P69 = N0 N1 Na Nk Nt Ns - 1.
```

At a zero all six factors are units. The consecutive-product Pell descent
excludes N0=-1, and Delta=0 or3 modulo4 excludes N1=-1.
Since `A0=Delta(f^2-1)` is0 or1 modulo4, `Ns=1+I^2-A0` is never3
modulo4; hence Ns=1 and A0=I^2. The auxiliary factor modulo4 is then
a square, so Na=1. The remaining index and transport units are
epsilon,nu with epsilon*nu=1.

For this product proof one must retain the `C=0` branch initially.
Transport of absolute value1 gives C>=0; the only C=0 case is
F=2,z=1,nu=-1. Use package06's weaker bounds

```
q(q^2-1) < R < q^4-q^3+q^2-1 < q^4-2.
```

They still give E>R+2 and a>R+2. The same bootstrap, ordinary rank,
positivity restoration and auxiliary step-down give p=R. Then the
first-index congruence is `2n=R+epsilon+vE`. Exclude v>=1 as above;
epsilon=-1 would give p=2n+1, while Pell duplication forces
`c>Ak>k(Y+1)`, contradicting `kY<c<k(Y+1)`. Thus epsilon=nu=1,
and C=0 disappears. Every equation of §2 follows. The reverse
implication is immediate multiplication.

Factor degrees are22,18,28,7,2,22, summing to99. The leading forms
are nonzero for every beta>0; their product is nonzero over the integer
polynomial ring. The final subtraction of1 does not change degree.
The literal evaluator costs69=39M+30A.

## 4. Retained auxiliary system:16 unknowns,7 equations, degree24,60 operations

Replace T by two positive unknowns o,j and put

```
V=of-c,      U=jc-R.
```

Keep the six equations of §2 with this V and append `U=V`.
There are sixteen unknowns. The source `retained16_system60.json`
has33 multiplications and27 additions/subtractions, total60.
Exact residual degrees are22,18,24,7,2,22,6.
Its sum of squares has degree48 and80 operations.

Completeness follows by the restored o,j from §2, or directly from
package06's normalized source. Soundness uses the same bootstrap and
ordinary rank lemma. Here `f>2c` gives `V=of-c>c>1` immediately,
and the equation U=V supplies the second congruence. Thus no quotient
positivity or integrality restoration is needed in its soundness proof.

## 5. Explicit32-variable23-quadratic construction

Retain the sixteen positive primary variables of §4:

```
J,F,alpha,z,f,h,i,o,j,s,w,tau,eta,zeta,y,gamma.
```

Adjoin these sixteen positive register variables:

```
N,E,P,c,a,X,D,C2,G,L,F2,V,g,I,Baux,Delta.
```

Only q=beta J+1, k=eta+zeta, H=4a+3, C=q-F-alpha are abbreviations;
each is affine. The literal23 quadratic equations are:

```
 1. L = q^2-1
 2. N = q(L+1)
 3. X = wq
 4. a = E+sN
 5. E = X(a-E)
 6. c = k(a-E)+eta
 7. P = E(c-eta)+k
 8. tau^2 = P(P-k)+1
 9. D = X+ac+gamma H
10. Delta = a^2+H
11. C2 = c^2
12. D^2 = Delta C2+1
13. k = jc-V+1+hE
14. G = (q-1)(q-F)+alpha
15. jc-V = LG+(MC+q MF)J
16. (K0+w)C+(q-F)-z(q-1) = 1
17. F2 = f^2
18. V = of-c
19. g = y^2-V^2
20. I = i C2
21. Baux = I^2
22. Baux = Delta(F2-1)
23. y^2-Baux g = 1.
```

Let r1,...,r23 be the left side minus right side of these equations.
The single polynomial is

```
Q32 = r1^2+...+r23^2.
```

It is an ordinary integer-coefficient polynomial of exact total degree4.
Every residual is quadratic, and only residual8 uses tau; the
coefficient of tau^4 in Q32 is1. Replacing every variable by n+1 gives
the same degree4 and32 unknowns over nonnegative integers.

### Projection and positive extension

Equations1-7 recover the shared q,X,Y,E,k,c,a with Y=a-E=sq^3>0.
The first norm is equation8, because P=Lfirst+k.
Equations9-12 recover the main root and main norm.
Define R=jc-V. Equation15 forces
`R=LG+(MC+q MF)J>0`, and equation13 is the original index equation.
The transport equation remains exact. Equations17-23 give the ordinary
strong norm and auxiliary norm; equation18 and the definition of R give
both positive auxiliary congruences. Projection therefore satisfies §4.

Conversely take any positive solution of §4 and assign all16 registers
their displayed values. The less immediate positivity conditions are:

* L=q^2-1>0 and G>0 by the transport/budget bounds;
* V>1 by the preceding retained-auxiliary proof;
* I>1 and Baux=I^2>1;
* the auxiliary norm gives `(Baux-1)(y^2-V^2)=V^2-1>0`, so g>0.

All others are positive sums or products. Thus the extension is positive,
and the projection/extension arguments prove equality of existential
solvability predicates. Sum-of-squares equivalence is immediate over the
integers. Therefore ZFC proves that Q32 has no positive integer solution
if and only if Con(ZFC).

### Where the two-variable saving comes from

Package08's normalized quartic lift used an extra register
`K=Delta c^2=D^2-1` because its strong multiplier was iK.
The ordinary strong multiplier is ic^2, so K and its defining equation
can be removed. Switching from the quotient T to retained o,j costs
one primary variable but removes V0=Tf-1, for no net change.
Then `R=jc-V` allows the packed index R to be substituted into both
the index and packing equations without increasing their degree.
This removes one more variable and equation. The result is32 positive
unknowns and23 quadratics, compared with34 and25 in package08.

## 6. Reproduction

Run, with Python3 and no third-party packages:

```
python3 build_systems.py
python3 quartic32.py
```

The first script emits the complete arithmetic DAGs and records exact
sparse-polynomial residual degrees, gate counts and liveness.
The second emits every expanded quadratic residual and checks all23
exact projection identities over an integer polynomial ring. It also
checks that every variable and fixed coefficient is live and verifies
the tau^4 degree certificate.

Relevant primary repository sources at the pinned revision are:

* `06-blank67/proofs/fixed_blank_67_proof.md`;
* `02-system63/PELL_INTERFACE_LEMMAS.md`;
* `02-system63/FIXED_INPUT75_ORDINARY_PROOF.md`;
* `07-fixed70/artifacts/fixed_input_notes.md`, transparent alternative;
* `08-start-only67/evidence/diophantine_zfc_encoding/start_only_quartic34_proof.md`.

All are under `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms`.
