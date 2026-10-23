# A deflated seventh-order polynomial majorant

## Result and its scope

The literal circuit `generated/order7_positive.json` is an ordinary integer
polynomial in the nine strictly positive variables

    b, g, h, s, w, C, i, j, n.

Its exact degree is **1,573,266**, and its division-free evaluator uses **504**
binary arithmetic operations: 168 additions, 29 subtractions and 307
multiplications. Constants and register reuse are free in this arithmetic
circuit measure. The nonnegative-coordinate translation has the same degree
and 511 operations. Fixed integer coefficients are supplied as actual bytes
and explicit recipes; no unresolved program-index parameter occurs.

The mathematical equivalence is to the complete positive source in package59
at commit `beb0192cb8dc36f78c369c080f2adfbc1887a486`. Its source compiler and
calibration then give, in ordinary mathematics formalizable in ZFC, existence
of a zero if and only if there is a finite syntactic ZFC refutation. Negation
gives the requested consistency equivalence. This does not decide either
side and is not a new end-to-end Lean or Rocq certificate.

Compared with package59's degree1,910,404 / 473-operation equation, the new
degree decreases by 337,138 (17.6474714249... percent), while the evaluator
uses 31 additional gates. This is a new degree/size tradeoff, not dominance
in both metrics or a global minimum claim.

## 1. Precisely inherited ingredients

All source registers, source positions, target positions, coefficient
bindings, the two-block binary encoding, free coordinate C, CRT absorption,
and the normalized margin are inherited unchanged from package59's
`nine_free_adjunct`. The complete proof is retained as
`upstream/FREE_COORDINATE_SOURCE_PROOF.md`. It supplies:

    A>=3, C>=1, J=4A-5, D=(A^2-1)C^2+1,
    e=iJC, E=eDC, F=(A^2-1)E^2+1,
    Lm=CD+1-A, G=A+F Lm, H=C+F(2R+1+(j-1)C),
    I=(G^2-1)H^2+1, a0=(P^2-1)K^2+1,
    V0=PK, Omega=Jm, E0=J(n+(bw)^2)+Q.

Here `m=K^2(4t-g)-16t(C-KY)^2`, `t=bB^116`. The fixed source parameters are

    B=2^2134939 b^2, N=2^17079501 b B^1201.

The four native coefficients are the entire original31 tuple, with radix
2^1064921 and shifted high-mask port. All four byte hashes are authenticated
in `coefficients/BINDING.json`. No port is mixed with a different tuple.

The source polynomial has the 89 records, 31 weights and 22 targets already
specified in `data/`. Its complete 22,544-interaction isolation certificate is
replayed by `check_source.py`. The inherited proof of unconditional source
positivity and bounded-word carry extraction is unchanged.

Package48 supplied the polynomial quotient approximation and its elementary
concavity argument. Package55 exposed an additional two-defect expansion.
Both are credited. The new contribution here is **deflation using the actual
Pell-parameter identity**, followed by a higher approximant whose remainder
has an exact positive-coefficient certificate. Neither changed source codes
nor a new compiler theorem is claimed.

## 2. The new majorant, with no divisions

Put `Nstar=2G+Lm` and define four polynomial quotients:

    N1=2e^2 D(D-1)Lm+3C,
    N2=2e^2(D-1)Lm,
    N3=2e^2(Lm-C),
    N4=2e^2 C.

Define the new polynomial

    T7 = e[(2048D^2-1024D-256)Nstar
           -128N1-80N2-56N3-42N4
           +i^2(1568-448A+288C)] +640i+4096.          (1)

Every displayed symbol abbreviates an ordinary integer polynomial. In
particular, the quotient expressions `N1,...,N4` are defined by their
division-free right sides; they do not add existential variables.

**Majorant theorem.** For every A>=3 and positive integers C,i, with the
above definitions,

    T7 > 4096 sqrt(DF) G > 0.                         (2)

This uniform inequality applies before a zero is decoded, including
arbitrarily large C and i. It is not an asymptotic assertion.

## 3. The new algebraic deflation

Let

    W=(40A-41)C^2+16, S=A-1-3C.

The relation J=4A-5 yields the exact identity

    e^2=16i^2D-i^2W.                                 (3)

This is the additional relation the older majorant did not use to simplify
its remainder. The four inherited quotient remainders are

    r1=3-A,
    r2=3CD+3-A,
    r3=2e^2(A-1)D^2+r2,
    r4=2e^2(1-A-C)D^3+r3,
    Nstar=D^j Nj+rj, j=1,2,3,4.

The old sixth-order polynomial part, before its correction, is

    U6=e[(1024D^2-512D-128)Nstar
          -64N1-40N2-28N3-21N4].

Set

    T6=U6-224i^2eS+560i^2e+320i+2048.

The subtraction cancels a complete high-degree part of the old quotient
remainder, by (3). Adding a fifth quotient `N5=32i^2C` and collecting terms
gives exactly

    T7=2T6-33eN5.

This identity is the compact way to obtain (1). The variable-dependent
subtraction is justified by the exact remainder certificate below; deleting
a positive padding term without that proof would not be valid.

## 4. Exact positivity certificate and proof of the majorant

Define

    tn7=2048D^7-1024D^6-256D^5-128D^4
         -80D^3-56D^2-42D-33,
    dn7=109824D^6+36608D^5+18304D^4+9984D^3
         +5460D^2+2772D+1089.

Exact multiplication gives

    tn7^2-2048^2 D^13(D-1)=dn7.                       (4)

For D>=1, tn7>0: the sum of its negative coefficients is 1619<2048.
Thus, for D>1,

    tn7/D^5 >2048D^2 sqrt(1-1/D).                    (5)

Let

    R7=D^5 T7-e tn7 Nstar.                           (6)

The file `data/order7_majorant_positive_certificate.json` lists exactly
264 terms with strictly positive integer coefficients, defining

    R7-4096D^5 = sum a_(u,v,w)(A-3)^u(C-1)^v i^w.    (7)

Every exponent is a fixed nonnegative integer. The checker reconstructs
the left side independently from (1), the definitions of D,e,F,G and (6),
then expands A=x+3 and C=y+1 and compares every coefficient with the file.
It also checks that the terms with u=v=0 contain a positive coefficient,
so the right side is strictly positive even at A=3,C=1. Equation(7) is a
finite algebraic positivity proof, not a collection of numerical samples.
Consequently R7>4096D^5 throughout the required domain.

For clarity, a compact exact recurrence for this finite certificate is

    tn6=1024D^6-512D^5-128D^4-64D^3-40D^2-28D-21,
    R6=D^4 T6-e tn6 Nstar,
    r5=Nstar-32i^2 C D^5,
    R7=2D R6+33e r5.

The existing elementary argument now applies with scale4096. Write
`X=e^2D^3(D-1)`, so DF=X+D, and use

    G=(X/D)Lm+CD+1.

The inequality sqrt(X+D)<sqrt(X)+D/(2sqrt(X)) gives

    4096 sqrt(DF)G
      <2048 eD^2 sqrt(1-1/D) Nstar+4096v,
    v=(CD+1)/(2eD sqrt(1-1/D))<1.

Here D>=A^2>=9 and e=i(4A-5)C>=7C; these imply the last bound directly,
as in the retained package48 proof. Equations(5)--(7) give

    T7=e(tn7/D^5)Nstar+R7/D^5
       >2048 eD^2 sqrt(1-1/D)Nstar+4096,

which proves(2). The divisions occur solely in the proof.

## 5. Final equation and both directions

Use the positive polynomials

    a1=4096^2 DFI, V1=T7 H,
    Theta=E0-Omega(V0+V1).

The proposed equation is

    F9=(Theta^2-Omega^2(a0+a1))^2-4Omega^4 a0a1=0.    (8)

From(2) and I<=G^2H^2, V1>sqrt(a1)>0. Also
V0^2-a0=K^2-1>0. These are unconditional strict majorants.

If m=0, then F9=E0^4>0 because

    E0=Jn+(J-2)(bw)^2+3bwC+2>0.

Otherwise real factorization of(8) yields signed real roots r0,r1 and

    n+(bw)^2+Q/J=m(V0+V1+r0+r1),
    r0^2=a0, r1^2=a1.

The parenthesis is positive by the strict majorants, and the left side is
positive by E0>0. Hence m>0 **before** using square-root integrality. The
unchanged margin argument then recovers C>2R+1+bw and C>K. It gives DFI>a0,
so a1>a0. The rational sum r0+r1=Theta/Omega is therefore nonzero. The
identity 2(r0+r1)r0=(r0+r1)^2+a0-a1 makes both roots rational and thus
integral; r1/4096 is an integral square root of DFI by the same rational-root
argument. The factor equation gives J|Q. These are exactly the unchanged
Jones ratio hypotheses, hence the unchanged decoded positive source zero.

Conversely, the source theorem provides ratio witnesses. Convert H by the
same exact CRT parameterization and choose positive integral roots. Set

    n=m(V0+V1+r0+r1)-(bw)^2-Q/J.

This is an integer and is positive. Indeed (bw)^2+Q/J<2D by the inherited
carrier bounds; F>D, so sqrt(DF)>D, and (2) implies V1>4096D. Since m>=1,
the stated n is positive. One real factor in(8) vanishes. Thus source
solvability and positive solvability of(8) are equivalent in both directions.

## 6. Exact degree, including the cancellation

The counted evaluator is(8), with504 live operations. A separate checking
circuit evaluates D^20 F9. It is not presented as the primary evaluator.

Let delta0=V0^2-a0 and delta1=V1^2-a1. Define

    Bsmall=E0^2-2E0 Omega(V0+V1)+Omega^2(delta0+delta1).

The exact two-defect identity is

    F9=Bsmall^2+4Omega^2 V0V1 Bsmall
        +4Omega^4(delta0 V1^2+a0 delta1).             (9)

For the majorant defect, the division-free identity is

    D^10(T7^2-4096^2 DFG^2)
      =e^2 dn7 Nstar^2
       +2048^2 D^10[X Lm^2-4DG(CD+1)]
       +2e tn7 Nstar R7+R7^2.                       (10)

Multiply(10) by H^2 and add 4096^2 DF D^10(H^2-1) to get D^10 delta1.
The certificate computes (9) after multiplying by D^20.

The unchanged exact degrees are

    deg A=18729, deg D=37460, deg e=18731,
    deg G=187303, deg H=158957, deg Omega=93880,
    deg V0=65303, deg V1=439911.

The new remainder has exact degree187305; its highest term as a polynomial
in A,C,i is 2880 A^10 C^12 i^3. The mixed term 2e tn7 Nstar R7 in(10)
uniquely dominates, giving degree655559 before cancelling D^10, hence
degree280959 for T7^2-4096^2DFG^2. Therefore deg delta1=598873,
deg Bsmall=786633, and the square of Bsmall uniquely dominates(9). This
proves exact degree1,573,266.

The generated degree certificate propagates total-degree upper bounds and
exact diagonal leading coefficients in two formal positive constants
a=2^2134939 and c=2^17079501. A positive nonzero diagonal leading coefficient
attains that upper bound for the actual constants. It is recorded verbatim
in `generated/order7_positive_degree.json`.

## 7. Reproduction and limitations

`python3 build.py` regenerates the two primary circuits, their certificate
circuits and degree ledgers. `python3 verify.py` checks the fixed tuple,
source isolation, positivity certificate, polynomial identities, literal
formula agreement, graph liveness, costs, degree and domain translation.
The arithmetic checks use Python's standard library and do not test whether
a ZFC refutation exists. They are evidence for the finite implementation;
the unbounded semantic theorem uses the named inherited compiler and ratio
results and the mathematical argument above.

The new components are AI-assisted research and were internally reviewed;
no external peer review or newly kernel-checked semantic theorem is implied.
