# One-factor saturation of the positive Pell certificate

## Results and precise boundary

The two new literal polynomials have the same nine strictly positive inputs
`b,g,h,s,w,C,i,j,n` as the frozen compact54-sharp H2082 construction:

* `saturated_positive.json`: 434 live binary arithmetic operations, exact total
  degree 1,628,768. Its natural translation has 441 operations.
* `saturated_radical_positive.json`: 1,074 operations, exact degree 1,103,950.
  Its natural translation has 1,081 operations.

The first improves both operation count and degree over the frozen
440-operation, degree-1,845,940 H2082 equation. The second improves both measures
over the incoming direct-majorant endpoint (1,753 operations, degree 1,158,228),
although that endpoint uses a different complete native coefficient tuple.
All counts charge live binary additions, subtractions and multiplications,
including squares and scalar products; constant numeral leaves and reuse are free.

These are new ordinary existential reductions. The source encoding and its
native/compiler-to-syntactic-refutation calibration are retained dependencies.
The argument is formalizable in ZFC once those specified interfaces are supplied;
this contribution does not create a new end-to-end Lean/Rocq or encoded internal
ZFC derivation. No consistency assumption, global optimum, or worldwide priority
claim is made. The new Pell representation and unbounded witness constructions
are proved below; finite checks only certify arithmetic transcription.

## 1. A modified two-witness Pell representation

Write `psi_A(t)` for the sequence 0,1,2A,4A^2-1,..., with recurrence
`psi_A(t+2)=2A psi_A(t+1)-psi_A(t)`; write `chi_A(t)` for its companion
with initial values 1,A. For A>=2, the positive solutions of
`x^2-(A^2-1)y^2=1` are `(chi_A(t),psi_A(t))`, t>=1.

**Theorem.** Suppose A,B,C,J are positive integers with

    A>=3, 1<B<A, C>B, J>=A.

Define, for i>=1 and j0>=0,

    D=1+(A^2-1)C^2, e0=i J C^2,
    F=1+(A^2-1)D e0^2,
    Lambda=CD+1-A, G=A+F Lambda,
    H=C+F(B+j0 C), I=1+(G^2-1)H^2.

Then `C=psi_A(B)` if and only if some i,j0 make DFI an integer square.

### Soundness

All D,F,G,H,I are positive. Indeed D>=A^2, and
Lambda>=A^2-A+1>0, so G>A. There are exact congruences

    F=1 (mod D), G=1 (mod D), I=1 (mod D),
    G=A (mod F), H=C (mod F), I=D (mod F).

Thus D,F,I are pairwise coprime. Their square product makes each an integer
square. Let d=sqrt(D)>0. The second square becomes

    F=1+(A^2-1)(i J C^2 d)^2.

Pell classification gives positive indices s,m,t with

    C=psi_A(s), i J C^2 d=psi_A(m), H=psi_G(t).

Here s>=2, because C>1. Since C>=3, J>=A, and d>=A,
`i J C^2 d>=9A^2>4A^2-1=psi_A(3)`; hence m>3.

The elementary Pell rank lemma says

    psi_A(s)^2 | psi_A(m)  implies  psi_A(s) | m.

For completeness, the standard divisibility law first gives s|m. Write m=su.
The addition identities give
`psi_A(su)=u chi_A(s)^(u-1) psi_A(s) (mod psi_A(s)^3)`.
Since `gcd(chi_A(s),psi_A(s))=1`, square divisibility implies
`psi_A(s)|u`, and therefore `C|m`. This argument also covers even C.

Since G=A modulo F and H=C modulo F, recurrence reduction gives
`psi_A(t)=psi_A(s) (mod sqrt(F))`. The classical index-separation lemma,
applied with parameter 2A and `sqrt(F)=chi_A(m)`, gives

    s=t or s=-t (mod 2m).

This particular index lemma also has a short elementary proof on A>=3.
Put x=chi_A(m). The addition identities give
`psi_A(t+2m)=-psi_A(t) (mod x)` and
`psi_A(2m-t)=psi_A(t) (mod x)`. Every index therefore folds to a representative
r in [0,m], with its residue equal to a signed psi_A(r) and its original
index congruent to r or -r modulo2m. The Pell identity implies
`x>2 psi_A(m)` because A>=3. All signed representatives lie strictly between
-x/2 and x/2. Equal residues must therefore be equal integers, and strict
growth of psi makes the two folded indices equal. This proves index
separation directly. No exceptional-index case is hidden. A primary-source
statement in a more general integral form is Sun, arXiv:2609.01594v1,
Lemma2.2; the classical positive-Pell facts are also collected in Fig.5 of
the CILC2015 proceedings, pp.15--16 of the PDF.

Now F=1 modulo C and G=1 modulo C, whereas H=B modulo C. Hence t=B modulo C,
and C|m gives `s=B or s=-B (mod C)`. For s>=2,
`psi_A(s)>=As`; combined with B<A, this yields `0<s+B<C`.
Thus s+B cannot be a nonzero multiple of C, and |s-B|<C. The only possible
congruence is s=B. Consequently C=psi_A(B).

### Completeness with an explicit finite-period construction

Assume C=psi_A(B), and let d=chi_A(B), so d^2=D. The matrix
`M_A=[[2A,-1],[1,0]]` has determinant one. Modulo the positive integer
`J d C^2` it therefore lies in a finite group. A positive multiple m of its
order satisfies `J d C^2 | psi_A(m)`. Choose

    i=psi_A(m)/(J d C^2)>0.

Then F=chi_A(m)^2. Construct G as above. Modulo F the matrix M_G also has
finite order T. For arbitrarily large integers t congruent to B modulo TC,

    H0=psi_G(t)=psi_G(B)=psi_A(B)=C (mod F),
    H0=t=B (mod C),

using G=A modulo F and G=1 modulo C. Since F=1 modulo C, the integer
`(H0-C)/F` is B modulo C. Take t large enough to make this quotient at least B,
and set `j0=((H0-C)/F-B)/C>=0`. Then H=H0 and I=chi_G(t)^2.
All three factors D,F,I are squares. This supplies actual witnesses and does
not rely on an unexplained cofinality assertion.

An even shorter map from any old certificate is available: its old norm is
`F_old=1+(A^2-1)D^2(i_old J C^2)^2`. Set `i=d i_old` in the new certificate;
then F,F_old and consequently G,H,I agree. This map is an existential
construction, not an integer-polynomial inverse on arbitrary assignments.

## 2. The fixed nine-input source and ratio registers

The literal source prefix is copied without modification from the repository
candidate at commit c1a102936aca437e9999530a0111e6ddab56dc6d. Its complete source
and layout are the files `data/H2082/{layout,kernels}.json`. The four coherent
compact54-sharp coefficient ports and eleven fixed circuit leaves are included
under `coefficients/` and `fixed/`; the MF port is already shifted once.

With the same weights, targets, source kernel Gsource, and two-block words
Scode,Tcode as that source, the defining prefix is

    Bcode=2^864026 b^2,
    L=b Bcode^2200, N=2^6480184 Bcode^1162,
    R=L(Scode+Tcode+1)-Scode-1, cap=b Bcode^116.

The source contracts include R,N>=8 and the required source/carry/binomial
equivalence; they are not inferred merely from finite sample evaluations.
Retain the ratio registers

    U=N^2 w, Y=N^2 s, M=RY,
    P=2M^2U, K=R+1+h(P-1), A=M(U+1), B1=2R+1,
    W1=bw, J=4A-5, Q=3W1 C-2(W1^2-1),
    a0=1+(P^2-1)K^2,
    m=K^2(4cap-g)-16cap(C-KY)^2,
    Omega=Jm, E0=J(n+W1^2)+Q, V0=PK.

All variables b,g,h,s,w,C,i,j,n are positive. Set j0=j-1 and substitute
B=B1 in Section 1's new certificate; call its product a1raw=DFI. R,N>=8
imply A>=33280, 1<B1<A, and J>=A on every ambient assignment. The margin,
once positive, gives C>B1+W1 and in particular C>B1. The order of proof
below establishes the margin before using the new representation theorem.

## 3. A cheap unconditional majorant and the 434-operation equation

Set

    T=A D e0, V1=T G H, a1=DFI,
    Theta=E0-Omega(V0+V1),
    F9=(Theta^2-Omega^2(a0+a1))^2-4Omega^4 a0a1.

The equation is F9=0. Every abbreviation is polynomial; no new variable is
quantified. The two exact defects are

    T^2-DF=D(D e0^2-1)>0,
    V1^2-a1=(T^2-DF)(GH)^2+DF(H^2-1)>0.

Thus V1>sqrt(a1)>0 on every ambient positive assignment. Also
`V0^2-a0=K^2-1>0`. These inequalities hold independently of any final zero.

The positivity-first norm proof is now unchanged in structure, but its
new Pell certificate is justified by Section 1 rather than silently inherited:

1. `E0=Jn+(J-2)W1^2+3W1 C+2>0`; hence a final zero cannot have m=0.
2. Factoring the real two-root norm gives signed roots r0^2=a0,r1^2=a1 with
   `E0/J=m(V0+V1+r0+r1)`. Strict majorants make the parenthesis positive
   for every sign choice, so m>0 follows before root integrality.
3. The inherited margin bound gives `|C-KY|<K/2` and the old carrier range
   `C>B1+W1`. Since A^2>P, D>C^2, F>=A^2, and I>=A^2, it also gives
   `DFI>C^2 A^4>K^2P^2>a0`.
4. The rational sum x=Theta/Omega=r0+r1 is nonzero. The identity
   `2xr0=x^2+a0-a1` makes both roots rational and therefore integral.
   The norm identity now implies J|Q.
5. Section 1 gives C=psi_A(B1). The unchanged arithmetic binomial/ratio
   bridge consequently recovers the source zero and its finite refutation.
   Equivalently, its original auxiliary Pell representation can be rebuilt
   by the same finite-period construction with modulus J D C^2.

Conversely, take the inherited canonical ratio witnesses from a source zero.
Replace its auxiliary i_old by sqrt(D)i_old to preserve its F,G,H,I, or use
Section 1 directly. Its other ratio conditions m>0, J|Q and a0 square remain
unchanged. Choose positive square roots and set

    n=m(V0+V1+sqrt(a0)+sqrt(a1))-W1^2-Q/J.

The inherited bound W1^2+Q/J<2D still holds. Since T=A D e0>2D, V1>2D,
and hence n>0. A norm factor vanishes. This proves both existential
implications with the specified source. Negating and composing with its
named refutation calibration gives the intended Con(ZFC) equivalence.

## 4. A majorant of the entire saturated radical

Here A,C,i,Z are independent indeterminates. Put J=4A-5, use Section 1's
other definitions, but put H=C+FZ, and write Qrad=DF[(G^2-1)H^2+1]. Its A-degree is 36 and its
leading coefficient is `(1024 C^19 i^5 Z)^2`.

Write Qrad=sum q_k A^k. Define the polynomial part of its positive formal
square root by the finite coefficient recurrence

    t18=1024 C^19 i^5 Z,
    t_(18-k)=(q_(36-k)-sum_(l=1)^(k-1) t_(18-l)t_(18-k+l))/(2 t18),
             1<=k<=18.

This discovery calculation takes place in Q(C,i,Z). All denominators and
negative exponents cancel after multiplication by `sigma=1024 C^5 i`.
The resulting P=sigma sum t_r A^r has 333 integer monomials. Its exact table
is `radical_P.json`. Set

    L0=2^20 C^24 i^6 Z, Pplus=P+L0,
    Delta=Pplus^2-sigma^2 Qrad.

The finite exact certificates prove:

* P(A+3,C+1,i+1,Z+1) has 6,650 positive coefficients, with constant
  15,915,642,730,652;
* Delta(A+3,C+1,i+1,Z+1) has 36,309 positive coefficients, with constant
  32,237,226,735,615,909,648.

Therefore, for all A>=3,C,i,Z>=1, Pplus>sigma sqrt(Qrad)>0. These are
universal integer-polynomial identities and coefficient positivity, not
asymptotic or sampled estimates. The uncorrected polynomial part is NOT a
majorant: its shifted defect has 28,788 negative coefficients and its value
at (3,1,1,1) is -1,140,296,347,768,021,232. The correction is essential.

For the second fixed equation substitute Z=B1+(j-1)C and use

    V1=Pplus(A,C,i,Z), a1=sigma^2 DFI,
    Theta=E0-Omega(V0+V1),
    F9=(Theta^2-Omega^2(a0+a1))^2-4Omega^4 a0a1.

Every operation in the supplied DAG is addition, subtraction or multiplication;
the coefficient recurrence is not evaluated using the current input values.
The proof of Section 3 applies word for word until square recovery. At that
point, r1/sigma is rational and its square is the integer DFI, so it is an
integer. Since sigma is a positive integer, the desired unscaled square is
recovered. For completeness F>D, so V1>1024 sqrt(DFI)>2D and n is positive.

## 5. Exact degrees, with cancellation resolved

The authenticated source has r=deg R=8799, nu=deg N=2324, W=116. Put
a=r+4nu+2=18097. Direct source leading terms are nonzero and positive; the
parent's degree certificate and all source leaves are retained.

Common degrees are

    deg Omega=5a+2W+3=90720,
    deg V0=3a+r+1=63091,
    deg delta0=deg(K^2-1)=3a+r+2=63092,
    deg E0=a+4=18101, deg a0=2 deg V0=126182.

For the cheap bound,

    deg V1=18a+r+24=334569,
    deg delta1=deg(V1^2-a1)=34a+2r+48=632944.

The latter follows from the exact defect above: its first summand has
the unique greatest degree and a positive leading coefficient.

For either equation define

    Bsmall=E0^2-2E0 Omega(V0+V1)+Omega^2(delta0+delta1).

The universal identity resolving all outer-norm cancellations is

    F9=Bsmall^2+4Omega^2 V0V1 Bsmall
             +4Omega^4(delta0 V1^2+a0 delta1).

For the cheap equation Bsmall^2 is uniquely dominant, with degree

    4 degOmega+2 degdelta1
      =92r+352nu+8W+284=1,628,768.

Its positive leading coefficient cannot cancel or vanish on the actual
coefficient tuple.

For the whole-radical equation, the unique greatest weighted monomials are

    [Pplus]_top=2^20 A^18 C^24 i^6 Z,
    [Delta]_top=2^41 A^18 C^48 i^12 Z^2.

Here A,C,i,Z have weights a,1,1,r. Consequently

    deg V1=18a+r+30=334575,
    deg delta1=18a+2r+60=343404,
    deg Bsmall=524844.

The four terms in the resolved identity have degrees

    1,049,688; 1,103,950; 1,095,122; 832,466.

The second is uniquely dominant and has positive leading coefficient.
Therefore the exact degree is

    59a+4r+8W+103=63r+236nu+8W+221=1,103,950.

The affine translation from nine positive inputs to nine natural inputs
preserves total degree. As in the parent, the natural j directly supplies
j0, while every other natural input is increased by one.

## 6. Reproduction, provenance, and verification scope

The baseline source parent is preserved in upstream/. `build.py` creates the
cheap literal DAGs. `build_radical.py` checks all24 multivariate Horner orders
and selects the least counted one; this is a finite circuit choice, not a
claim of globally optimal evaluation. Its winning order is Z,i,C,A.

`discover_radical.py` independently derives the uncorrected polynomial part
with rational arithmetic; the release verifier checks the complete delivered
integer-polynomial identities and positivity using a separate implementation.
Source prefix structural identities, literal coefficient hashes, topology,+liveness and domains are verified. Finite Pell examples and modular checks
are supplementary diagnostics, not proofs of the general theorem or of
consistency. The proofs in Sections1--5 address the unbounded new steps.

Primary arithmetic sources:

* Z.-W. Sun, https://arxiv.org/html/2609.01594v1 , Lemmas2.1--2.2.
* CILC2015 proceedings, https://ceur-ws.org/Vol-1459/ProceedingsCILC2015.pdf ,
  Fig.5 (Pell divisibility/index identities) and accompanying references.
* J.P. Jones, *Universal Diophantine Equation*, J. Symbolic Logic47 (1982),
  549--571, https://doi.org/10.2307/2273588 .

The claim is a new explicit relative construction composed with the exact
inherited native tuple and source theorem. It is not a substitute for completing
the repository's remaining internal-model semantic calibration.
