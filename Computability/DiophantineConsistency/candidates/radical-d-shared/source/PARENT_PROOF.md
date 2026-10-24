# A direct radical majorant in nine positive unknowns

## Result and scope

The literal integer-coefficient polynomial `equation9.json` has nine strictly
positive unknowns `(b,g,h,s,w,C,i,j,n)`, exact total degree **1,158,228**, and
**1,753** live binary arithmetic operations. Named registers are abbreviations,
not quantified unknowns. Source71 has degree1,379,730 in478 operations. This is
a **degree improvement with a larger evaluation circuit**, not simultaneous
dominance and not a claim of global minimality or literature priority.

The four original31 native coefficients and the source/ratio prefix of source71
are retained unchanged. Composing the new elementary arithmetic lemma below with
that prefix's ordinary source-to-refutation theorem yields, by mathematics
formalizable in ZFC,

    ZFC proves: [there is no positive zero of this polynomial] iff Con(ZFC).

The present package does not supply a new end-to-end Lean/Rocq or object-language
ZFC proof. The exact native compiler and syntactic refutation dependencies are
those stated by the retained source65, ratio59, and nine71 proofs. The new
unbounded step is proved below; finite checks authenticate its coefficients and
algebra. No assumption that ZFC is consistent is used.

## 1. The local polynomial

Temporarily regard A,C,i,Z as independent indeterminates. Define

    J=4A-5, D=(A²-1)C²+1,
    e=iJC, E=eDC, F=(A²-1)E²+1,
    L=CD+1-A, G=A+FL, H=C+FZ,
    I=(G²-1)H²+1, Q=DFI.

As a polynomial in A over Q(C,i,Z), Q has degree46 and leading coefficient
`(1024 C^24 i^5 Z)^2`. The unique formal square root with leading term
`1024 C^24 i^5 Z A^23` has an A-polynomial part T. This is only a finite way to
discover and specify coefficients: no numerical approximation, variable
exponent, oracle, or formal-series quantifier occurs in the final equation.

For an explicit finite definition, write Q=sum q_k A^k. Put

    t23=1024 C^24 i^5 Z,
    t_(23-k)=[q_(46-k) - sum_(ell=1)^(k-1)
                         t_(23-ell)t_(23-k+ell)]/(2t23),  1<=k<=23.

These are23 operations in a rational-function coefficient field, independent of
any unknown value. Exact coefficient arithmetic proves that

    P(A,C,i,Z)=65536 C^7 sum_(r=0)^23 t_r A^r

belongs to Z[A,C,i,Z]. Its654 nonzero integer coefficients are listed in
`data/radical.json`; the authoritative division-free circuit evaluates exactly
that table. Every denominator in T is cleared by65536 C^7. In particular there
is no remaining division by A,C,i, or Z in the equation.

Set

    Delta=P² - (65536 C^7)² Q.

The complete integer expansion of Delta has3781 terms and coordinate degrees
at most `(22,42,10,2)` in `(A,C,i,Z)`. The following two finite polynomial
identities are checked by regeneration and by an independent sparse-ring audit:

* `P(X+3,Y+1,i,Z)` has1816 strictly positive coefficients.
* `Delta(X+3,Y+1,U+1,V+1)` has32637 strictly positive coefficients. Its constant
  coefficient is295870595720775501924817.

The full coefficient lists are in `certificates/P_shifted.json` and
`certificates/defect_shifted.json`. Each equality is an identity over Z, not a
finite sampling result. Verifying it means ordinary finite polynomial expansion;
all coefficients, exponents and signs are supplied.

### Uniform majorant lemma

For every A>=3 and C,i,Z>=1,

    P(A,C,i,Z) > 65536 C^7 sqrt(DFI) > 0.

Proof. J>0,D>0,F>0, and CD+1-A>0 (already C=1 givesA²-A+1>0), so G>A>=3,
H>0 and I>0. The first coefficient identity, evaluated at X=A-3,Y=C-1,
shows P>0; the nonnegative variables i,Z are in fact positive. The second,
evaluated at X=A-3,Y=C-1,U=i-1,V=Z-1, gives Delta>0 because all monomials
are nonnegative and the constant is strictly positive. Thus P² exceeds the
positive radicand square scale, and the positive branch yields the claimed
strict inequality. This proof uses no asymptotic estimate.

## 2. Explicit replacement in the fixed nine-variable equation

The source65 encoding and the source71 ratio registers R,N,t,U,Y,M,P0,K,A,B1,W1,
J,Q0,D,E,F,G,H,I,a0,Omega,E0,V0 are unchanged. To avoid a clash, P0 denotes
the inherited ratio register formerly called P; P denotes the new654-term
majorant polynomial. The exact definitions occur in `upstream/nine71_PROOF.md`
and in the copied, pinned arithmetic circuit `upstream/nine71.json`.

The new registers are simply

    Z=B1+(j-1)C,
    scale=65536 C^7,
    V1=P(A,C,i,Z),
    a1=scale² DFI,
    Theta=E0-Omega(V0+V1).

The new ordinary polynomial is

    F9=(Theta²-Omega²(a0+a1))² -4 Omega^4 a0 a1.

The old i is the unscaled free positive unknown; the local e=iJC exactly
matches the inherited register k. Also H=C+FZ, so the radicand in the local
majorant lemma is exactly the inherited DFI, not an approximation or a variant.
The source quantities satisfy R,N>=8 and hence A=RY(U+1)>=3 before assuming
F9=0. C,i>=1 and Z=B1+(j-1)C>=1 hold on every ambient positive assignment.
Thus the uniform lemma applies before any sign is inferred from the equation.

## 3. Soundness and completeness of the replacement

The unchanged first radicand has V0²-a0=K²-1>0 and V0>0. The new lemma gives
V1>sqrt(a1)>0. If the inherited margin m vanishes, Omega=Jm=0 and F9=E0^4,
which cannot vanish because

    E0=Jn+(J-2)W1²+3W1C+2>0.

At any zero with m nonzero, the real two-root norm factorization gives signed
real roots r0²=a0,r1²=a1 such that

    E0/J = m(V0+V1+r0+r1).

The strict majorants make the right parenthesis positive for every sign choice.
Consequently m>0, before using root integrality. The unchanged free-carrier
margin argument then recovers C>K and the inherited carrier range, and gives
DFI>a0. As scale>=65536, also a1>a0. Therefore r0+r1=Theta/Omega is rational
and nonzero. The identity

    2(r0+r1)r0=(r0+r1)²+a0-a1

makes both roots rational; each is integral because its square is integral.
Now r1/scale is a rational number with square DFI, so it too is integral.
This is the only issue caused by making the scale a polynomial in C, and
positivity and integrality of scale settle it completely. The norm identity
then gives J|Q0 exactly as in source71. All original ratio conditions follow,
hence the source zero and a syntactic ZFC refutation follow.

Conversely take a positive source zero and the unchanged constructive ratio
witnesses. Both original radicands are integer squares; scaling the DFI root
by65536 C^7 preserves this. With positive roots r0,r1 choose

    n=m(V0+V1+r0+r1)-W1²-Q0/J.

It is integral. The inherited bound W1²+Q0/J<2D remains unchanged. Here F>D
and I>=1, hence sqrt(DFI)>D, and the new majorant yields V1>65536D>2D.
Since m>=1 this n is strictly positive. A norm factor vanishes and F9=0.
Thus the new and old zero-existence statements are equivalent. The unchanged
native-source/refutation calibration supplies the displayed consistency
biconditional after negation.

## 4. Exact degree: the dominant term changes

The local bounds must not be inserted into source71's old degree formula:
the largest term of the outer norm changes. Let

    r=degR=7963, nu=degN=2115, W=116,
    a=degA=r+4nu+2=16425.

Source register degrees are

    degOmega=5a+2W+3=82360,
    degV0=3a+r+1=57239,
    deg(K²-1)=3a+r+2=57240.

The unique highest weighted-degree monomial in P is
`2^26 A^23 C^31 i^5 Z`; since degZ=r, it gives

    degV1=23a+r+36=385774.

The unique highest weighted-degree monomial in Delta is
`141664530202624 A^22 C^42 i^10 Z²`, giving

    degdelta1=22a+2r+52=377328,
    delta1=V1²-a1.

Let delta0=V0²-a0=K²-1 and define

    Bsmall=E0²-2E0 Omega(V0+V1)+Omega²(delta0+delta1).

Its degree is542048. The following exact universal polynomial identity resolves
all cancellations in the outer norm:

    F9=Bsmall² +4Omega²V0V1 Bsmall
          +4Omega^4(delta0 V1²+a0 delta1).

The four summands, splitting the last parenthesis, have exact degrees

    1084096, 1149781, 1158228, 821246.

The unique dominant summand is4Omega^4 delta0 V1². Its coefficient cannot
cancel with any other summand. Therefore

    degF9=72r+276nu+8W+224=1158228.

For a positive symbolic source-leading triple (rho,sigma,tau) for R,N,t,
the diagonal leading coefficient is `2^90 tau^4 rho^72 sigma^276`.
In source65 put alpha=2^2134939 and c=2^17079501; then
rho=2alpha^3981,sigma=c alpha^1057,tau=alpha^116, and the coefficient is

    2^162 alpha^578828 c^276 >0.

This proves the exact degree for the actual fixed native coefficients, not
just a formal upper estimate.

## 5. What the finite artifacts establish

The regenerated local polynomial and shifted certificates prove the local
identities and positivity. Independent sparse arithmetic checks them without
SymPy. The literal circuit checker verifies that the new V1 is exactly P at the
four correct named registers, that the full tail equals the displayed norm,
that the old prefix is preserved, that fixed leaves are bound to the complete
original31 tuple, and that the circuit contains1753 charged binary gates.
A cancellation-resolved degree receipt checks the integer degree arithmetic
and the unique highest weighted monomials. Modular examples detect transcription
errors but are not substitutes for those exact identities or for the written
unbounded proof. No finite computation is presented as a consistency test.
