# Independent audit of the nine-positive order-seven majorant

Internal AI-assisted mathematical review of `nine/build.py`, `nine/PROOF.md`, and the frozen `nine/generated/order7_positive.json`. This is not external peer review or a new proof-assistant certificate. The independent finite checker is `reviews/check_nine_independent.py`; it imports neither the construction nor its verifier. Run `python3 reviews/check_nine_independent.py` from the archive root; all data paths are resolved relative to the script, so an absolute-path invocation from another directory also works. Its checks remain active under `python3 -O`.

## Verdict and scope

The new majorant, positivity-first finalizer, and exact degree reduction are valid relative to the explicitly inherited package59 source compiler, numerical Jones ratio theorem, coefficient binding, and free-carrier transport. The nine-positive equation has exact degree **1,573,266** and the frozen primary arithmetic circuit reports **504** live binary arithmetic operations. The change improves degree from package59's 1,910,404 while adding 31 operations; it is a tradeoff, not dominance or a global minimum result.

The main issue needing care is the order of implications. The majorant must hold for every free positive carrier C before the final equation forces the source range. It does. The margin sign is then recovered before square-root integrality or any old carrier bound is invoked. I found no circular bootstrap in the new proof.

## 1. Independent literal majorant identity and positivity certificate

For A>=3 and positive integers C,i, set

    J=4A-5, D=(A^2-1)C^2+1, e=iJC,
    L=CD+1-A, F=e^2 D^2(D-1)+1, G=A+FL,
    Nstar=2G+L,
    N1=2e^2D(D-1)L+3C,
    N2=2e^2(D-1)L,
    N3=2e^2(L-C), N4=2e^2C.

The exact polynomial from the frozen builder is

    T7=e[(2048D^2-1024D-256)Nstar
          -128N1-80N2-56N3-42N4
          +i^2(1568-448A+288C)]+640i+4096.

I independently constructed T6 from its literal sixth-order polynomial part with the correction

    i^2 e [560-224(A-1-3C)]+320i+2048,

then checked the exact identity T7=2T6-1056i^2eC against the frozen compressed expression. In particular, the older intermediate correction constant 640 is not the one used here; the final folded builder correctly corresponds to 560.

Define

    tn7=2048D^7-1024D^6-256D^5-128D^4
         -80D^3-56D^2-42D-33,
    R7=D^5T7-e tn7 Nstar.

Expanding the literal left side of

    R7-4096D^5

and substituting A=x+3, C=y+1 independently produced exactly the 264 coefficients in `nine/data/order7_majorant_positive_certificate.json`. Every coefficient is a strictly positive integer; the smallest is 128. The terms independent of x,y are exactly

    293313636 i^3 + 49748823 i.

Thus the certificate is strictly positive even at A=3,C=1, and

    R7>4096D^5

holds uniformly throughout the required domain. The check did not infer positivity from samples or from the remainder recurrence alone.

Independent exact multiplication also verified

    tn7^2-2048^2 D^13(D-1)
      =109824D^6+36608D^5+18304D^4+9984D^3
        +5460D^2+2772D+1089.

The negative coefficients of tn7 have absolute-value sum 1619<2048. For D>=1 this gives tn7>0, and consequently, for D>1,

    tn7/D^5 > 2048D^2 sqrt(1-1/D).

## 2. Uniform majorant before decoding

Here D>=A^2>=9, e>=7C, L>0 and G>0 hold without any final-zero assumption. Set

    X=e^2D^3(D-1), v=CD+1.

Then DF=X+D and G=(X/D)L+v. The strict concavity bound

    sqrt(X+D)<sqrt(X)+D/(2sqrt(X))

therefore gives

    4096 sqrt(DF)G
      <2048eD^2 sqrt(1-1/D)Nstar+4096v0,
    v0=(CD+1)/(2eD sqrt(1-1/D)).

Since sqrt(1-1/D)>1/2, CD+1<2CD and e>=7C, we have v0<2/7<1. Combining this with the exact tn7 inequality and R7>4096D^5 yields

    T7>4096 sqrt(DF)G>0.

This is a uniform inequality for arbitrarily large positive C,i; no old carrier range, carry extraction, square-root integrality, or asymptotic estimate appears in its proof.

## 3. Soundness and completeness of the final norm

Write a0=(P^2-1)K^2+1, a1=4096^2DFI, I=(G^2-1)H^2+1, V0=PK, V1=T7H and Omega=Jm. The inherited definitions give H>1 unconditionally. Consequently

    V0^2-a0=K^2-1>0,
    V1>4096 sqrt(DF)GH>=sqrt(a1)>0.

With E0=J(n+W1^2)+Q and Q=3W1C-2(W1^2-1), the exact expansion

    E0=Jn+(J-2)W1^2+3W1C+2>0

holds for every positive assignment, including free C=1. If the proposed norm vanishes, m=0 is impossible because it would reduce the norm to E0^4. Otherwise real factorization gives signed real roots r0,r1 and

    n+W1^2+Q/J=m(V0+V1+r0+r1),
    r0^2=a0, r1^2=a1.

The left side is E0/J>0, and the right-hand parenthesis is positive by the two strict majorants. Hence m>0 before any integrality assertion.

From m=K^2(4t-g)-16t(C-KY)^2>0 with t,g>0, we obtain |C-KY|<K/2. The inherited unconditional Y>=64, K>=P+R, P>U>=W1 then imply

    C>K(Y-1/2)>2K>2R+1+W1.

This restores the old carrier range. The inherited inequalities A^2>P, D>C^2, F>=A^2, I>=G^2>=A^2 then give DFI>a0 and thus a1>a0. The rational sum r0+r1=Theta/Omega is nonzero. The identity

    2(r0+r1)r0=(r0+r1)^2+a0-a1

makes both roots rational. Rational square roots of integers are integers, so r0,r1 are integral, and the rational square root r1/4096 of DFI is also integral. The factor equation then yields J|Q. These are exactly the old ratio hypotheses. The rest of the decoding is the unchanged source theorem.

Conversely, the old source/ratio theorem supplies the required positive witnesses and CRT transport. Choosing positive integral roots and setting

    n=m(V0+V1+r0+r1)-W1^2-Q/J

gives an integer. The old unconditional inequalities A>W1, D>=A^2 and D>C^2 imply W1^2+Q/J<2D. Also F>D, hence the new majorant gives V1>4096D. Since m>=1, the new n is strictly positive. The factor equation holds exactly, proving completeness. No cofinality assumption on the shifted CRT coordinate is added.

## 4. Exact denominator clearing and degree

I independently verified the following polynomial identity in the formal ring Z[D,e,L,v,R7], with G=e^2D^2(D-1)L+v and Nstar=2G+L:

    D^10(T7^2-4096^2DFG^2)
      = e^2 dn7 Nstar^2
        +2048^2D^10[X L^2-4DGv]
        +2e tn7 Nstar R7+R7^2.

The equality uses D^5T7=e tn7 Nstar+R7 and the exact tn7 square identity above. No hidden division occurs in the checking circuit. Multiplying by H^2 and adding 4096^2DFD^10(H^2-1) gives exactly D^10(V1^2-a1).

I also independently verified the final two-defect identity in six unrelated formal variables E0,Omega,V0,V1,a0,a1. If delta0=V0^2-a0, delta1=V1^2-a1 and

    Bsmall=E0^2-2E0Omega(V0+V1)+Omega^2(delta0+delta1),

then the primary norm equals

    Bsmall^2+4Omega^2V0V1Bsmall
      +4Omega^4(delta0V1^2+a0delta1).

The certificate circuit therefore computes exactly D^20 times the primary equation. Since D>=9 on the domain, this multiplication introduces no zero there; as nonzero polynomials, their degrees differ by exactly 20 deg D.

Independent expansion of the new remainder gives its unique weighted leading term

    2880 A^10 C^12 i^3,

of degree 187305 for weights deg A=18729, deg C=deg i=1. The decisive source degrees and their propagation are

    deg D=37460, deg e=18731, deg Nstar=187303,
    deg H=158957, deg Omega=93880,
    deg V0=65303, deg V1=439911.

The mixed term 2e tn7 Nstar R7 uniquely dominates the majorant-defect identity at degree 655559. Removing D^10 gives degree 280959 for T7^2-4096^2DFG^2. Thus delta1 has degree 598873, Bsmall has degree 786633, and Bsmall^2 uniquely dominates the final identity at degree 1573266. The generated checking circuit has degree 2322466, exactly 1573266+20*37460, and reports no unresolved positive-degree cancellation.

## Dependencies and limits

This audit concerns the new majorant and its mathematical integration. It does not independently reprove the old arithmetic compiler, the complete Jones ratio theorem, K215's relation to finite syntactic ZFC refutations, or their formalizability in ZFC. The four original31 coefficient ports are inherited together, and the frozen builder must continue to authenticate that complete tuple and its source records. No variable exponentiation, extra existential register, or free program index occurs in the new equation.
