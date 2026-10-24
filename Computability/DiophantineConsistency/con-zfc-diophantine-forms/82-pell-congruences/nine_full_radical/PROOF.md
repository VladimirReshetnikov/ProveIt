# A majorant for the complete Pell radical

## Result

The explicit polynomial in `laurent9_positive.json` has nine strictly positive
integer unknowns, exact total degree **1,158,228**, and a division-free evaluator
with **726** live binary additions, subtractions, and multiplications. Constants
and register reuse are free under this circuit convention. The evaluator has
430 multiplications, 265 additions, and 31 subtractions.

Its positive solvability is equivalent to positive solvability of package 71's
pinned native source. Consequently, with the inherited native compiler and
K215/refutation calibration, ZFC proves its unsolvability equivalent to
Con(ZFC). This is a lower-degree, higher-operation-count alternative to package
71's degree 1,379,730 / 478-operation equation, and not a claim of global
minimality or a new variable-count bound. The degree decreases by 221,502.

The new ingredient is a polynomial upper bound for the **whole** radical
sqrt(D F I). Approximating sqrt(D F) G first and then multiplying by H magnifies
the error by a high-degree polynomial. The present construction avoids that
magnification. No newly unbounded computational search or unspecified
universal-polynomial index occurs.

## 1. The universal algebraic lemma

Treat A,C,i,t as real numbers satisfying A>=3,C>=1,i>=1,t>=3, and put

    D=(A^2-1)C^2+1,   e=i(4A-5)C,
    F=(D-1)e^2D^2+1, L=C D+1-A,
    G=A+F L,          H=C+F t,
    I=(G^2-1)H^2+1.

Let T0 be the integer polynomial given by the 654 coefficient records in
`laurent_candidate.json`, key `majorant`, in the coordinate order (A,C,i,t).
The same file lists the complete expanded radical DFI and exact defect

    Delta0 = T0^2 - 2^32 C^14 D F I.

These are literal integer coefficient tables, not sampled evaluations. The
definition may alternatively be stated as

    T0 = 2^16 C^7 [A^{>=0}] sqrt(D F I),

where the formal Laurent square root at A=infinity has leading term
2^10 C^24 i^5 t A^23. This latter description motivates the construction;
the coefficient table is its division-free, integer-polynomial definition.
The equality follows, without convergence issues, because the table has that
leading term and its displayed defect has A-degree22.

**Lemma.** Throughout the stated real domain,

    T0 > 2^16 C^7 sqrt(D F I) > 0.

**Finite algebraic proof.** Substitute A=x+3, C=y+1, i=z+1, t=u+3.
The complete expansion of T0 contains 9,216 nonzero coefficients, all strictly
positive. The complete expansion of Delta0 contains 32,637 nonzero
coefficients, all strictly positive. Both constant coefficients are positive.
The file `laurent_cone_certificate.json` supplies the two complete expansions;
`verify.py` independently reconstructs D,F,G,H,I from their definitions, checks
the exact defect, re-expands both substitutions, and compares every coefficient.
Thus T0>0 and Delta0>0 when x,y,z,u are nonnegative. Also D,F,G,H,I are positive:
D>=9, e>=7C, L=CD+1-A>0, G>1, and H>0. Taking positive square roots gives the
claim. All of these are finite polynomial identities and ordered-ring
arguments, formalizable in ZFC. No numerical sampling enters this proof.

The multiplication by C^7 is useful: it clears the variable denominators in
the Laurent polynomial without increasing its A-degree. A constant-only
denominator clearing would not do so.

The delivered evaluator uses

    S=2^18 C^7,   T=4T0,

which obey the same strict inequality T>S sqrt(DFI). The additional constant
factor four permits a smaller evaluation formula in the already available
register J=4A-5. In particular, writing T7 for package 71's previous majorant,
the evaluator uses

    T=64 C^7 (T7-640i-4096)H - Corr(J,C,i,t,D).

`laurent_correction_nopad_4JDbasis.json` defines Corr by 110 integer coefficient
records, in the indicated five-coordinate order. The independent checker
expands J and D and proves this formula equals 4T0 exactly. This optimized
formula is an evaluator, not an additional mathematical assumption.

## 2. The complete nine-variable polynomial

Keep every source and Pell register of package 71's pinned polynomial up
through a0, Omega, E0, G, H, I. Their exact source DAG is included at
`upstream/71-determinant-guards/nine_positive/generated/composed9_positive.json`.
The variables, in order, are

    b,g,h,s,w,C,i,j,n > 0.

The whole original31 fixed tuple is supplied under
`upstream/31-sun10/coefficients/payloads/`, with its generator, exact byte hashes,
literal transition and tile tables, and proof of coefficient binding.
In particular MF_source is already shifted; no coefficient port is free or
silently exchanged for a smaller tuple.

For clarity, the unchanged source registers use a=2^2134939,c0=2^17079501:

    B=a b^2, ell=sum B^w_l, Targets=sum B^q_l,
    Us=ell+g, Gs=(D2(B)Us+D1(B))Us+D0(B), N0=B^117,
    Mask=N0-1-(b-1)ell,
    Sc=g+N0(2Gs+Targets), Tc=Mask+N0(B-2)Targets,
    Ls=b B^1991, R=Ls(Sc+Tc+1)-Sc-1,
    N=c0 b B^1057, cap=b B^116.

The 31 weights, 22 targets and three exact integer coefficient kernels are
included unchanged from source65. Then

    U=N^2w, Y=N^2s, M=RY, P=2M^2U,
    K=R+1+h(P-1), A=M(U+1), B1=2R+1, W1=bw,
    J=4A-5, Q=3W1 C-2(W1^2-1),
    D=(A^2-1)C^2+1, e=iJC, E=eDC,
    F=(A^2-1)E^2+1, L=CD+1-A,
    G=A+FL, t=B1+(j-1)C, H=C+Ft,
    I=(G^2-1)H^2+1, a0=(P^2-1)K^2+1,
    V0=PK, m=K^2(4cap-g)-16cap(C-KY)^2,
    Omega=Jm, E0=J(n+W1^2)+Q,
    S=2^18 C^7, a1=S^2 D F I,
    T=4T0(A,C,i,t), Theta=E0-Omega(V0+T).

The proposed equation is

    P9=(Theta^2-Omega^2(a0+a1))^2-4Omega^4 a0 a1=0.

All capital letters are polynomial abbreviations, not additional unknowns.
The full literal DAG in `laurent9_positive.json` is authoritative.

## 3. Soundness, including the order of sign recovery

The inherited source estimates are unconditional for positive inputs: R>=1
and A>=3. Hence t=2R+1+(j-1)C>=3, and the universal lemma applies before a
source zero has been decoded. It gives T>sqrt(a1). Also V0>sqrt(a0), since
V0^2-a0=K^2-1>0.

If m=0, then P9=E0^4, which is nonzero because

    E0=Jn+(J-2)W1^2+3W1 C+2 > 0.

Otherwise the real factorization of P9 yields signed real roots u0,u1 with
u0^2=a0, u1^2=a1 and

    E0/J = m(V0+T+u0+u1).

The parenthesis is strictly positive by the two unconditional upper bounds.
Thus m>0. This step precedes any use of rational square-root integrality.
The unchanged free-carrier margin argument now gives C>K and C>B1+W1,
and then DFI>a0. Since S>=1, a1>a0. The rational sum u0+u1 is nonzero, and

    2(u0+u1)u0 = (u0+u1)^2+a0-a1

shows both roots are rational and therefore integral. The rational number
u1/S squares to the integer DFI, so it is an integer too. The factor equation
also recovers J|Q exactly as in the inherited norm proof. The resulting ratio
conditions give the binary base, the binomial divisibility condition, and the
encoded positive source zero. The detailed unchanged proofs are included from
packages59,65,71; the new argument changes only the strict majorant and its
integral square scale.

## 4. Completeness

From a positive source zero, the inherited theorem supplies the ratio witnesses
and positive integral roots r0=sqrt(a0), r1=sqrt(DFI). Set

    n=m(V0+T+r0+S r1)-W1^2-Q/J.

This is an integer and makes one real norm factor zero. It is positive: the
inherited bound W1^2+Q/J<2D holds, while F>D, I>=1, and
T>S sqrt(DFI)>S D>2D, with m>=1. Thus every positive source zero lifts to a
positive zero of P9. The new polynomial and the pinned source have equivalent
existence statements. Composing with the native compiler and K215/refutation
calibration gives the requested object-theoretic equivalence in ZFC.

## 5. Exact total degree

The unchanged source values give

    r=deg R=7963, q=deg N=2115, a_deg=deg A=16425,
    deg K=28620, deg V0=57239,
    omega=deg Omega=82360, deg E0=16429.

The leading T0 monomial is 2^26 A^23 C^31 i^5 t. Thus

    deg T = 23 a_deg+r+36 = 385774.

The highest weighted monomial of Delta0 is

    141664530202624 A^22 C^42 i^10 t^2,

with positive coefficient. The other terms have strictly smaller degree
after the stated substitution. Therefore, for delta1=T^2-a1,

    deg delta1=22 a_deg+2r+52=377328.

Put delta0=V0^2-a0=K^2-1 and

    Bsmall=E0^2-2E0 Omega(V0+T)+Omega^2(delta0+delta1).

The exact two-defect identity is

    P9=Bsmall^2+4Omega^2 V0 T Bsmall
             +4Omega^4(delta0 T^2+a0 delta1).

Its four candidate degrees, with the last parenthesis separated, are

    1084096, 1149781, 1158228, 821246.

The unique highest term is 4Omega^4 delta0 T^2, **not** Bsmall^2.
Consequently the exact degree is 1,158,228. On the full positive diagonal
its leading coefficient is

    2^166 a^578828 c0^276 > 0.

This establishes attainment of the degree for the actual fixed coefficient
tuple. The program verifier checks the source leading terms, the complete
defect table, the candidate degrees, and this leading coefficient.

## 6. Status and further questions

The new majorant, its optimized evaluation identity, and the exact degree are
finite algebraic theorems with complete integer certificates. The source
compiler and refutation calibration remain explicitly inherited ordinary
mathematical proofs; this package is not a new end-to-end Lean/Rocq build or
an exported object-language ZFC derivation. The displayed theorem neither
assumes nor establishes Con(ZFC).

Natural next questions are whether the 110-term correction can be evaluated
more cheaply, whether a tighter simultaneous majorant for both norm roots can
lower the now-dominant delta0 T^2 term, and whether the same full-radical method
improves the ten-integer finalizer. No affirmative result on those questions is
claimed here.
