# Folding the main root into the first Pell norm

This is a new ordinary existential reduction on nine **strictly positive**
integer variables. It retains the entire original31 or compact54-sharp tuple
of the reviewed position-zero source. No ports are mixed or recalibrated.

| Whole tuple | Live binary operations | Exact total degree | Previous parent |
|---|---:|---:|---:|
| original31 | 414 = 242 mul + 152 add + 20 sub | 1,355,142 | 419 / 1,472,168 |
| compact54-sharp | 422 = 246 mul + 156 add + 20 sub | 1,497,238 | 427 / 1,626,248 |

The two new equations are `boundary_simple.json` and `compact_simple.json`.
They are not pointwise identical to their parents: the positive auxiliary
witnesses i,j,n are reconstructed. The proof below establishes both directions.
Fixed leaves, source words, masks, rank and threshold are retained literally.
The source-to-machine/refutation interpretation remains the already reviewed
ordinary dependency. This packet supplies no new native calibration, Lean
proof, internal object-ZFC derivation, consistency assumption, or optimum claim.
Lean remains paused.

## 1. The retained source and ratio boundary

The immutable parents are `candidates/position-zero-norm-sharing/` and the
nine-positive component of `ConZFC_Constructive_Reductions_2026-10-23.zip`,
SHA256 `37e6f0e8d46fec88df60eab7d4c4b5106fc321be1736763d5def910b8d0619e0`.
The accepted ordinary review is `reviews/constructive-nine-peer.md`; the
new `SOURCE_PINS.json` pins its bytes and the exact two immediate parents.
The archive's `nine/report_section.tex` explains position-zero normalization,
complete fixed-tuple binding, the source/binomial bridge and cofinal packing.
The retained inert numerical ratio interface is
`nine/inherited/NineRatio.lean`; no proof assistant or emitter is executed.
The saturated ancestor `candidates/saturated-nine/source/PROOF.md`, Sections
2--3, states the same ratio boundary and explains positivity-first extraction.

Keep the parent's source polynomials R,N and cap, and put

```
U=N²w, Y=N²s, M=RY, P=2M²U,
K=R+1+h(P−1), A=M(U+1), B1=2R+1,
W=bw, J=4A−5, Q=3WC−2(W²−1),
a0=1+(P²−1)K²,
m=K²(4cap−g)−16cap(C−KY)²,
Omega=Jm, E0=J(n+W²)+Q.
```

Every variable b,g,h,s,w,C,i,j,n is positive. The unchanged source prefix
has the ambient bounds R,N≥8 and b≤R,N. These bounds are a retained source
contract, rather than a new claim about arbitrary four port values.
The retained numerical ratio theorem has the following exact boundary:

* a0 is a square, C=psi_A(B1), m>0 and J divides Q imply the binomial/source
  condition; the source decoder then gives a source zero;
* a source zero has cofinally large binary packing choices b, positive g,
  and positive ratio witnesses h,s,w,C satisfying precisely these conditions.

Neither direction assumes b divides g or R+1. The position-zero fifth source
residual excludes the all-one source, so the cofinal packed g can be positive.
Only this frozen source boundary is inherited; all modified root work is below.

Useful ambient consequences follow without interpreting any root. We have
A≥33280, 1<B1<A, J>A, and A>W: indeed
A=R N²s(N²w+1)>R N⁴w≥b N⁴w>bw.
Also P>R+1 and K≥R+P>B1. If m>0, cancellation of the positive cap gives
|C−KY|<K/2, hence C>K(Y−1/2)>K>B1.

## 2. The new two-root equation

Define polynomial abbreviations

```
Delta=A²−1, e=iJC²,
F=1+Delta*a0*e²,
Lambda=1+A(C−1), G=A+F*Lambda,
Z=B1+(j−1)C, H=C+FZ, I=1+(G²−1)H²,
a=a0*F, V=A*a0*e, Vhat=GH,
Theta=E0−Omega*(V+Vhat).
```

The new equation is

```
(Theta²+Omega²(a−I))²−4Omega²*a*Theta²=0.                 (1)
```

Its complete six-term expansion is also
`(Theta²−Omega²(a+I))²−4Omega⁴*a*I`. Integer literals and fixed leaves
are free; every live addition, subtraction and multiplication counts,
including squares and scalar multiplication. The emitted schedule shares
a0*e between F and V. The previous independent main root
D=1+Delta*C² and the previous product DFI do not occur in (1).

On every ambient assignment, a0≥1, e≥J≥A≥3, Lambda≥1 and Z≥B1≥2.
Thus F>a0, G>F and H>1. In particular I≥G²>F²>a0F=a: the radicands
are unequal, before using any zero or Pell conclusion. The two exact defects
are

```
V²−a = a0*(a0*e²−1) > 0,
Vhat²−I = H²−1 > 0.                                   (2)
```

## 3. Soundness, with the order of hypotheses explicit

First, E0 is strictly positive without a margin or a root hypothesis:

```
E0=Jn+(J−2)W²+3WC+2>0.
```

If Omega=0, the left side of (1) is E0⁴, so a zero has Omega≠0.
Factor the complete two-root norm over the real numbers. Some signs give

```
E0 = Omega*(V+Vhat ± sqrt(a) ± sqrt(I)).                 (3)
```

By (2), every parenthesized expression is positive. Therefore Omega>0,
and m>0. The preceding margin calculation now gives C>B1>1.
This establishes the required size condition before any Pell classification.

Equation (3) also makes a signed sum of the two roots rational. It is nonzero
because a≠I. Squaring and rationalizing that sum shows each root is rational;
a rational root of an integer square is an integer. Hence both a=a0F and I
are squares. Since F=1 modulo a0, gcd(a0,F)=1; prime valuations now show
that a0 and F are individually squares. Write tau²=a0 and f²=F with
positive tau,f. The recovered ordinary Pell equation is

```
f²−Delta*(e*tau)²=1,
C² divides e*tau, e*tau≥C.
```

Classify it as f=chi_A(q), e*tau=psi_A(q), q≥1. Likewise I being a square
and G≥3 give H=psi_G(t), t≥1. Since G=A modulo F and H=C modulo F,
recurrence reduction yields psi_A(t)=C modulo f.

For clarity, the precise folding argument is elementary. Modulo
f=chi_A(q), the addition identities give

```
psi_A(t+2q) = −psi_A(t),
psi_A(2q−t) = psi_A(t).
```

Every index therefore has a representative r∈[0,q], with residue a signed
psi_A(r), and original index congruent to r or −r modulo 2q. All signed
representatives lie in (−f/2,f/2), because
f>2*psi_A(q) for A≥3. Since 0<C≤psi_A(q)<f/2, congruence forces
C=psi_A(p) for some 1≤p≤q and t=±p modulo 2q. Since C>B1>1, p≥2.

The square-ordinate rank fact gives C divides q. Here is the needed proof,
including even C. Strong divisibility of the positive Pell sequence gives
p divides q; write q=pu. Expanding
`(chi_A(p)+C*sqrt(Delta))^u` modulo C³ gives

```
psi_A(pu) = u*chi_A(p)^(u−1)*C modulo C³.
```

C² divides psi_A(q), while gcd(chi_A(p),C)=1, so C divides u, hence q.
Strong divisibility itself follows from the addition identities and the
Euclidean algorithm on indices; strict growth identifies the common index.
No parity or odd-index normalization is required.

On the other hand F=1 modulo C and Lambda=1−A modulo C, so G=1 modulo C.
The recurrence at parameter 1 gives psi_G(t)=t modulo C, while H=B1 modulo C.
Thus t=B1 modulo C. Combining with t=±p modulo 2q and C|q yields
p=±B1 modulo C. For p≥2, psi_A(p)≥A*p; because B1<A,
0<p+B1<C and |p−B1|<C. The only possible congruence is p=B1.
We have recovered C=psi_A(B1).

Finally (3) has integer roots, hence E0 is divisible by J; consequently
J divides Q. Together with the already recovered a0 square and m>0,
these are exactly the retained source/ratio conditions in Section 1.
No main-root square or quotient integrality was assumed during folding.

## 4. Completeness: actual positive i,j,n

Take the source and ratio witnesses supplied by Section 1. Thus
C=psi_A(B1), tau²=a0 with tau>0, m>0 and Q/J integer.
The determinant-one recurrence matrix

```
M_A = [[2A,−1],[1,0]]
```

is invertible modulo the positive integer J*C²*tau. In its finite matrix
group choose a positive period q, so J*C²*tau divides psi_A(q).
Set i=psi_A(q)/(J*C²*tau)>0. Then e*tau=psi_A(q) and F=chi_A(q)².
This construction permits arbitrarily large positive period multiples;
it does not assume an unproved cofinal divisibility assertion.

Form G as above. Let T>0 be a period of M_G modulo F. For arbitrarily large
t=B1+k*T*C we have

```
H0=psi_G(t)=psi_G(B1)=psi_A(B1)=C modulo F,
H0=t=B1 modulo C.
```

Because F=1 modulo C, the integer z=(H0−C)/F is B1 modulo C.
Choose t large enough that z≥B1, and set j=1+(z−B1)/C≥1.
Then H=H0 and I=chi_G(t)². Both roots of a=a0F and I are positive integers.

It remains to choose positive n, rather than merely an integer. Put
Dproof=1+Delta*C² for this inequality only; it is absent from the circuit.
The bounds e≥J*C²>C and a0≥1 give F>Dproof. Since Z≥2 and G≥3,
Vhat=GH>2F>2Dproof. We also have, on every ambient assignment,

```
W²+Q/J < A²+3C < 2+2(A²−1)C² = 2Dproof.                (4)
```

For the first inequality use A>W≥1 and J>A, dropping the nonpositive
`−2(W²−1)/J`. For the second write C=1+x, x≥0: the difference between
the right side and A²+3C is
`A²−3+(4A²−7)x+2(A²−1)x²>0`.
Now choose

```
n=m*(V+Vhat+sqrt(a)+sqrt(I))−W²−Q/J.
```

All terms are integers; m≥1, Vhat>2Dproof and (4) give n>0.
Equation (3) holds with the two plus signs, so (1) vanishes.
The two maps leave b,g,h,s,w,C unchanged and choose new positive i,j,n.
The retained source choices are cofinal in b, so the new reduction has the
same existential source zero condition in both directions.

## 5. Exact total degree, without expanding a million degrees

Let r=deg R, aDeg=deg A and Wmax be the largest source weight. To avoid
confusing a radicand with a degree, write aDeg as d in this paragraph.
The retained source has d=r+4*deg(N)+2. The full table is checked from every
literal node; the relevant exact degrees are

```
a0: 6d+2r+2, e: d+3, F:10d+2r+8,
Lambda:d+1, G:11d+2r+9, Z:r, H:10d+3r+8,
Vhat:21d+5r+17, a:16d+4r+10, V:8d+2r+5,
Omega:5d+2Wmax+3, E0:d+4.
```

Put dc=V²−a=a0(a0e²−1), di=Vhat²−I=H²−1, and

```
Bsmall=E0²−2E0*Omega*(V+Vhat)+Omega²*(dc+di).
```

The complete polynomial (1), by an exact ring identity, is

```
Bsmall² + 4Omega²*V*Vhat*Bsmall
        + 4Omega⁴*dc*Vhat² + 4Omega⁴*a*di.              (5)
```

The four degree upper bounds are respectively

```
60d+12r+8Wmax+44,
69d+13r+8Wmax+50,
76d+14r+8Wmax+56,
56d+10r+8Wmax+38.
```

The third is strictly largest. Its leading homogeneous term is exactly
`4*LH(Omega)^4*LH(a0)^2*LH(e)^2*LH(Vhat)^2`, which is nonzero.
The independent checker propagates full literal syntactic degree bounds
and exact highest homogeneous diagonal values with the complete actual
fixed integers. A nonzero diagonal leading value modulo a prime proves
that homogeneous component is nonzero over the integers. This supplies
an exact lower bound, not a sampled or syntactic degree claim. Three primes
are recorded as redundant diagnostics; one nonzero value suffices.

For original31, (d,r,Wmax)=(16357,7931,115), giving 1,355,142.
For compact54-sharp they are (18069,8787,115), giving 1,497,238.
The larger raw DAG bounds, 1,860,748 and 2,055,916, are deliberately not
reported as the actual degrees.

## 6. Executable scope

`build.py` only clones the needed frozen source registers and writes the
new local schedule; `check.py` does not import that builder. It verifies
all source-node remaps, local polynomial formulas, complete coverage,
topology/liveness/counts, the exact norm/defect/centered identities and
actual-coefficient degree witnesses. The complete four port values and
all fixed leaf magnitudes are bound to the earlier whole tuples through
the reviewed archive checker; no fixed value is replaced by a checksum.
Finite folding, valuation and sign diagnostics supplement, rather than
replace, the unbounded proof. Mutations of the final norm, a retained
fixed leaf, the saturation factor and a prefix map must be rejected.
Both normal and optimized Python modes are run. No Lean or old native/H10
emitter is invoked.
