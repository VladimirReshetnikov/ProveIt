# Thirteen integers by an interval-weighted approximation guard

## Statement

Keep the B4 front end and all Jones ratio registers of SIGNED_B4_PROOF.md. Set

 cap=b B^t, delta=C-KY,
 Delta=g(cap-g)K^2-cap^2 delta^2.

Replace the separate g>=1 and old margin>0 guards by the single condition Delta>0. The complete remaining guard list is s>=1, phi>=0, Delta>0. This requires three Pell-stack variables instead of four, hence thirteen unrestricted integers. No change to the imported Jones ratio theorem and no Sun2026 theorem is required.

## Soundness of the merged guard

Since epsilon!=0, b=2 epsilon^2>=2>0, so cap>0. If Delta>0, K!=0 and g(cap-g)>0; therefore0<g<cap. Moreover the elementary identity

 4g(cap-g)=cap^2-(cap-2g)^2 <= cap^2

implies4(C-KY)^2<K^2. These conclusions hold for signed integer g,K,C,Y and do not assume positivity of K.

With the remaining guards s>=1,omega=w^2>=1,phi>=0, the front end gives R>=N>=8 and b<=N<=R. The positive C,Y together with the strict approximation force K>0, and the existing square-gap argument gives h>=1. Reflect i to|i| and use the j Pell orbit exactly as before.

For complete precision when invoking the unchanged source Nine.ratio_sound, supply its free ceiling parameter as

 Gaux=8gK^2+1.

The integer d=K^2-4(C-KY)^2 is at least1, hence its margin is

 Gaux*d-8gK^2 >=1>0.

All other ratio quantities are independent of that ceiling parameter. Therefore the literal theorem applies with Gaux and yields b a power of two and N^2|binomial(2R,R). This Gaux is a proof-side polynomial abbreviation, not a quantified variable of the output. The stronger recovered bound g<cap supplies all bounds needed by the fixed-polynomial carry argument, so it recovers a zero of the source quartic.

## A strengthened bound for the actual completeness witness

This uses the actual source construction, not an arbitrary ratio solution. Exact source: Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Ratio.lean at22e75dd6b87b1b199bb08c778d7cf075ae5aae08, copied in upstream/Ratio.lean.

- exists_B25core, lines434–442, fixes b=2^k, omega=2^(2R+1-k), U=N^2 omega, with k<2R+1. Thus

 U=(N^2/b)2^(2R+1).

- Lines454–470 construct Y=Q=floor(rho), where rho=(U+1)^(2R)/U^R, Q=binomial(2R,R)+w' U, and M=RY. The defining binomial split, stated as lemma_2_24 and rho_split_c in the same source, gives

 rho=Y+f, 0<=f<2^(2R)/U=b/(2N^2).

For an explicit proof of the strict bound, expand (U+1)^(2R). The terms of index below R, divided by U^R, sum to f. Each such reciprocal power is at most1/U, and the sum of their positive binomial coefficients is strictly below2^(2R). Since b<=N and N>=8, f<1. The other terms give the displayed integer Q. Its divisibility by N^2 follows because both the central coefficient and U are divisible by N^2. In particular Y is the same quotient/floor witness as in the source and Y>=1.

- ratio_core in Ratio.lean, lines83–151, used by exists_B25core at lines517–518, states

 |C-K rho| <= 2K rho R/A,
 A=RY(U+1), K>0.

Divide by K and use rho=Y+f, Y>=1,0<=f<1:

 |C/K-rho| <= 2(Y+f)/(Y(U+1)) <4/U.

Consequently the triangle inequality gives the needed bound relative to Y, not merely to rho:

 |C/K-Y| <= |C/K-rho|+f
 <4/U+b/(2N^2)
 =(b/N^2)(4/2^(2R+1)+1/2)
 <b/N^2,

because R>=8 (indeed R>=2 is already enough). This proof does not claim Y or s is a square, and it does not change any canonical witness.

## Completeness of the merged guard

For a coded quartic witness, 1<=g<cap=bB^t. Also cap<=N and b<=N, directly from N=2B^(9t+2). The strengthened estimate gives

 cap^2(C-KY)^2/K^2 < cap^2 b^2/N^4 <=1.

Meanwhile g and cap-g are positive integers, so g(cap-g)>=1. Therefore

 Delta/K^2=g(cap-g)-cap^2(C-KY)^2/K^2 >0.

This establishes the new guard for the very same canonical witness used by the old completeness argument. The chosen odd base exponent still makes omega a square. All other witnesses are unchanged.

## Finalizer and variables

Use d1=3s-1,d2=3phi+2,d3=3Delta-1 and the same linear-prefix stack

 C0=1, Bj=1+4dj C_(j-1)zj^2, Cj=C_(j-1)Bj, Cstar=C3.

Set Z=epsilon w i z1z2z3 and keep the same intersective merger and three-root norm from SIGNED_B4_PROOF.md. Its proof requires only that each discriminant is2 modulo3, each zj is nonzero, and |Cstar|>1; these remain true with three guards. The exact variable list is

 (epsilon,g,h,s,w,phi,i,j,z1,z2,z3,residue,normroot) in Z^13.

Both directions above prove that its integer solvability is equivalent to that of the source31 quartic and hence to a finite ZFC refutation. Negating gives its integer unsolvability equivalent to Con(ZFC), provably in ZFC. The stronger approximation estimate and the interval-weighted guard are ordinary mathematical proofs, not newly compiled Lean theorems.

## Exact circuit metrics

The finalized circuit has1409 live binary operations:489 additions,24 subtractions and896 multiplications. Its exact degree is370496t+84272=226334238192 at t=610895. Named degrees are Delta=2032t+464, Cstar=2032t+484, Smerge=31320t+7111, weight2=3760t+878, A2norm=92624t+21068. The output leading term is A2norm^4; the symbolic leading-head certificate tracks every fixed leaf and leaves a nonzero scalar times a positive base_scale power. Compared with the14-integer variant this saves one variable and11 operations at a0.0173% degree increase.
