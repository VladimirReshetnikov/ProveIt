# Independent review of the T16 approximant

The T16 refinement is sound under the same positive source domain as the preceding reviews. It improves the defect degree without introducing a variable, division, or a new semantic hypothesis.

Define polynomial registers

    e=iJC,
    L=CD+1-A,
    G1=e^2*D*(D-1)*L+C,
    S16=e*((16D^2-8D-2)*G-G1),
    V16=S16*H,
    a1new=256DFI.

The relation `F=(D-1)D^2e^2+1` and the definition `G=A+FL` give exactly

    G=D*G1+1.

## Exact defect identity

The polynomial defect is

    deltaDF=S16^2-256DFG^2
       =e^2*((20D^2+4D+1)*G1^2
             +(32D^2+24D+4)*G1+32D+4)
          -256D*G^2.

Multiplying by H and using `I=(G^2-1)H^2+1` gives

    deltaV=V16^2-256DFI
          =deltaDF*H^2+256DF*(H^2-1).

Both displayed expressions are integer polynomials. An explanatory rational expression, not part of the output equation, is

    T=16D^2-8D-2-1/D,
    S16=e*(T*G+1/D).

Direct expansion gives

    T^2-256D^3*(D-1)=20+4/D+1/D^2.

For D>=2, T>0. Therefore

    deltaDF>(20e^2-256D)*G^2.

Expanding this rational identity with G=DG1+1 gives the exact polynomial certificate above, including the middle coefficient `32D^2+24D+4` and constant `32D+4`.

## Strong domain bound

R,N>=8 and positive w,s imply U,Y>=64, M=RY>=512, and

    A=M(U+1)>=33280.

Since `e=i(4A-5)C`, with i>=1, and `D=(A^2-1)C^2+1`,

    e^2-14D
       >=[2A^2-40A+39]*C^2-14 >0.

The last inequality already holds for A>=20 and C>=1. Thus

    deltaDF>24D*G^2>0.

## Required root gap

S16 is positive, since its rational explanatory expression has positive terms. It is also strictly smaller than `16eD^2G`. Therefore, with Bstar=P(P+R),

    deltaV/V16 > 3GH/(2eD)
                > 3(D-1)D e/2
                > D^2
                > 2Bstar.

Here `G>F=(D-1)D^2e^2+1`, H>=1, D>=2, and e>=7 establish the middle inequalities; `D>2P` and R<P establish the last one. Also V16>Bstar because S16>1 and G>Bstar.

Consequently

    (V16-Bstar)^2>256DFI,
    sqrt(256DFI)<V16-Bstar.

The lower bound `sqrt(256DFI)>Bstar` follows from the preceding lower bound on sqrt(DFI). Thus this replacement preserves the h-weight radical separation and the integer centering bound `Z>=2Mdiv+h+1`.

Scaling a1 by 256 preserves its integer-square predicate, since 256 is 16 squared. The margin m is still the computed polynomial, and completeness still sets `n=mZ-Mdiv-v/u` with its actual positive value.

## Degree and leader

With the same source degree t and packing width W,

    deg(G1)=83t+18, lc(G1)=2^145.

The unique leading term of deltaV is

    20 e^2 D^2 G1^2 H^2.

Its degree is

    (20t+6)+(40t+8)+(166t+36)+(6t+2)=232t+52,

and its leading coefficient is

    20*2^(38+68+290+10)=5*2^408.

The negative term `256DG^2H^2` has degree 232t+50, so it cannot cancel that leader. The remaining defect term `256DF(H^2-1)` has degree 106t+24.

The resolved inner finalizer has unique leading term `Omega^2 h^2 deltaV`, degree `462t+6W+116` and coefficient `5*2^830`. The other three resolved terms have the same lower degrees as before. Squaring therefore gives

    degree = 924t+12W+232,
    diagonal leading coefficient = 25*2^1660.

The final subtracted norm term has degree only `820t+12W+208`. Thus the displayed total degree is exact, assuming the retained source degree/leader facts. The literal circuit and resolved certificate should be compared independently after emission.

## Conclusion

No defect was found in the T16 adapter or its degree calculation. The roots, signs, fixed margin, domains, and inherited semantic dependency chain are preserved.
