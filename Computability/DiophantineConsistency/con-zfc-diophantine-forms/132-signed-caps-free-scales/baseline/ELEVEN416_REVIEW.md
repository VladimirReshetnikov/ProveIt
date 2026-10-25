# Focused ordinary-proof review of the degree-416 route

Source root: `extracted/ConZFC_Unified_Binomial_Even_Indices_Round15_2026-10-24/ConZFC_Unified_Binomial_Even_Indices_Round15_2026-10-24/`.
Inspected: `scalar/CRT_CARRIER_PROOF.md`, `norm_weak/DEGREE_PROOF.md`, `scalar/PROOF.md`, and the signed-rank step in `scalar/source/centered11-proof.md` §5.2.

## Verdict and scope

No flaw was found in the new weak-Y carrier bootstrap or its exact degree argument. This is a focused ordinary-proof inspection, not a new complete audit of the native coefficient/calculus calibration. The live count 125 was independently checked from the literal DAG. The leading-form proof was read and its degree arithmetic checked, not computationally re-executed through imported checkers.

## Essential formulas

Y=qv, X=q(12w+4), a=(X+1)Y, H=4a+3, Delta=(a+2)^2−1,
I=rc², Df=1+Delta I², Q=Delta²I², delta=Q−1,
V=Df(c−R+4IT)−c, Cy=QV²−1, Da=delta Cy,
M=2q², Dcar=HM,
zc=Dcar T+MK+H(v−q²),
Ac=(zc²+3Dcar²)(zc³−19Dcar³),
S=srH M⁵, Z=S(n+QV)−Ac,
u=9S²Df, b=S²Da, e=81S²Pg.

The output is the full three-root norm
P=[(Z²−u−b−e)²−4(ub+ue+be)]²−64ubeZ².

## Correct bootstrap order

1. H and M never vanish. The homogeneous intersective quintic Ac has no rational zero. Thus S=0 makes P=Ac⁸≠0, and any zero has s,r nonzero.
2. Df,Da are positive even if c=0 (in that case I=Q=0 and Da=1). If c≠0, I=rc² gives |I|≥c², Df>|c|+1, so the integer-distance argument proves V≠0 and Da>0.
3. A negative guard root would be the unique imaginary term, impossible. Hence Budget>0 and, by its parity, Budget≥4.
4. Modulo three the radicands Df,Da,Dt are 1. The three radical weights 3,1,9 have distinct 3-adic orders, so every squareclass contribution is integral. Coprimality splits Pg=DtDg. This obtains S|Ac before invoking adjacent-Pell descent or excluding c=0.
5. Since H≡3 modulo q, q≡2 modulo3, and H is odd, gcd(H,M)=1. M⁵|Ac and monicity of its lowest-valuation zc⁵ term force M|zc, hence M|v−q². This restores Y=q³(2v_old+1).
6. The restored nonzero cubic scale and the budget exclude c=0. Only now invoke rational adjacent-Pell integrality, signed ranks, and the weaker H|K⁵ main projector.

The unusual zero-Y case is deliberately handled rather than silently inherited. The 3-adic separation does not require Pg to be prime to3: its squared order is at least4, while the other orders are0 and2; any shared irrational squareclass still has a unique least valuation.

## Why obvious substitutions do not prove an improvement

### I=rc is not presently licensed

The signed-rank theorem uses c²|I to conclude c divides the strong Pell index m. If |c|=Y_p(B), composition gives I=|c|Y_D(v), m=pv and D²−1=(B²−1)c². The extra factor c forces c|Y_D(v), and because Y_D(v)≡vD^(v−1) modulo c with gcd(D,c)=1, it forces c|v and hence c|m. This transfers the folded auxiliary congruence from modulo m to modulo c. Merely c|I yields p|m but does not yield c|m. Any lower-degree I needs a genuinely different folding theorem or an independently encoded replacement divisibility. Evenness of the source index alone does not supply this factor.

### Changing k's modulus does not lower degree416

Here deg(XY)=4, so k=R+1+hXY already has degree5, tied with R. Replacing XY by4q⁴ keeps degree5, unlike the cubic-Y family where it lowers degree7 to5. It may change gate counts but is not an automatic degree gain.

### Y=v predicts degree404 but breaks the proof

A syntactic experiment with Y=v and M=2q³ gives a centered-degree prediction404, because Df,Q,V,Da become smaller. However H=4(X+1)v+3 is no longer automatically coprime toq, so M|zc does not imply M|v−q³. Common prime factors of H andM are a genuine obstruction; one cannot assume the desired scale first to establish their coprimality. This is a research lead only, not a candidate with a proved consistency interpretation.

### M⁴ instead of M⁵ loses exact modulus recovery

From M⁴|Ac the valuation argument gives only 5 v_p(zc)≥4 v_p(M), not v_p(zc)≥v_p(M). The strict odd-multiplier scale and exclusion of v=0 are then no longer proved. A lower exponent would require new rank estimates and a separate nonzero mechanism, not cosmetic cancellation.

## Exact degree check

In the delivered weak route:
deg S=16, Df=14, Q=22, V=19, Da=82, Pg=62;
deg b=114, e=94, u=46.
Centering cancels Z²−b to degree at most92. The inner paired norm has uniquely dominant term −4be of degree208, while the final correction has degree368. Thus deg P=416, with leading form16 b_top² e_top².

The source displays an attained coefficient at
j^224 w^56 v^52 C^16 s^12 r^24 c^32,
namely2^400 3^290 beta^224>0; exponent sum416. It also gives the h^12 endpoint, avoiding any assumption that the two degree-five terms of k fail to cancel. There is no exact-degree gap in the printed argument.
