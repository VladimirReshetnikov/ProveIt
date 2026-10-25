# Aligning the amplification exponent with a strict beta quotient range

This is the final semantic delta to `ORIENTATION_FIRST_PROOF.md` and its fully stated signed-anchor dependency `PROOF_315.md`. The primary released endpoints are `strict_dimension_centered`, `strict_grouped_centered` and `strict_sparse_centered`. Their exact (variables, rows, degree, monomials, height) counts are (282,192,4,5491,128446), (287,197,4,4313,128446), and (309,219,4,3922,128446). The 283-variable separated-pool point is an additional measured diagnostic, not needed to define these three equations.

## Exact changes to the arithmetic interface

Replace K=2(2+t+x+y+F) by K=x. Tighten only the two beta quotient ranges for u and vq: replace their binomial lower index x+1 by x, so the decoded quotients lie in 0<=u,vq<x. The existing q^(x+1) denominator request becomes q^x. All other range lower indices, every numerator, and all other arithmetic equations remain unchanged. The N=B^K and q=(B*H0)^K requests now use the already existing x-index principal pair. The old independent K pair and its duplicate A*Y norm wire are aliased to that pair; their duplicate norm and multiplication definition are deleted. There are fourteen, not fifteen, independent principal pairs, while the exact power-request count remains eighteen.

The literal source transformation records each alias and both deleted rows. The independent checker reconstructs these changes from the old and new norm identities, not from a free-form assertion. The raw power, seed, index, amplification, radix and affected range metadata are updated together. The ordinary bound R=2+t+x+y+F remains a mathematical majorant; it is no longer the amplification exponent.

## Noncircular power and endpoint recovery

All initial frame and squared-anchor arguments in the orientation-first proof still apply. The frame uses the actual new exponent x, not an obsolete x+1 or K atom. All classified signed indices are bounded before any arithmetic signs are recovered. Every pooled error proof may use the conservative upper count m<=15, although the actual count is fourteen.

Initially t>=16, B>=1 and q>=2 are supplied exactly as before. Canonical orientation gives V0=(F^2+1)^t. The raw ceiling gives F>=1, B>=2, q>=3, and y=V0(V0-1)>F+2. The denominator request now has base q>=3 and exponent x. The negative-index power lemma therefore forces x>=0 and gives q^x exactly.

From x=F+1+(y+1)u0, a negative u0 would give x<=F-y<0, so u0>=0 and x>=F+1>=2. The last endpoint x=1+[1+(t+1)y]ut then gives ut>=1 and

    x>=2+(t+1)y.

Thus K=x>=2 is known before using the B^K and (B*H0)^K requests. They give N=B^x and q=(B*H0)^x. The remaining canonical-power and postponed interval-sign arguments are unchanged. In particular q>=B^2>V0 still follows from the raw ceiling, so the exact factorial digit and fixed point give F=t! without any circular use of the new majorant.

## Amplification, precision and radix bounds

After F=t!, the endpoint bound and y>=F+1 give

    x-(2+t+y+F)>=t(y-1)-F>0.

Hence R=2+t+x+y+F<2x. Also x>=F+1>=16!+1>2^32. Let E=8388608=2^23, the unchanged checked local-polynomial majorant exponent. For every real x>=2^32,

    E log_2(2x)<x.

For an elementary discrete proof, if 2^(n-1)<x<=2^n with n>=33, then E log_2(2x)<=2^23(n+1)<=2^(n-1)<x. The middle inequality holds at n=33 and is preserved when n increases because its right side doubles while n+1 increases by one. At x=2^32 directly E*33<2^32. Therefore the exact inherited local bound gives

    L<R^E<(2x)^E<2^x=2^K.

This is the same strict amplification inequality required for residue extraction and Horn-flow decoding, now with K=x.

Every range lower index k is at most K. The two changed ones equal x. The others are t, t+1 and y+1, all less than x by x>=2+(t+1)y and y>=1. Consequently the original precision 2K and loss at most k-1<K still suffice. No new divisibility assumption or larger CRT precision is needed.

The self-radix argument for zero representatives is exactly the repaired argument in `ORIENTATION_FIRST_PROOF.md`: the encoded index is positive after the factorial interpretation, H0>=2, and ordinary coefficients are bounded using max(1,a). The derived-label estimate h<=H0^ell also remains valid. The retained factorial inequality ell(t+1)<2F, with ell=4194304, now combines with x>=2+(t+1)y>2F to give ell(t+1)<K. Thus every required derived-label coefficient still lies below H0^K<=q.

## Constructive completeness for the strict ranges

Begin with the same finite refutation, cofinal t, F=t!, beta base y and beta-CRT code x. The first and last endpoint equations supply x>0. For each genuine beta step the canonical quotients have the form

    u=(x-S)/(1+(i+1)y),
    vq=(x-Sp)/(1+(i+2)y),

with S,Sp>=0, i>=0 and y>=1. Both denominators are at least two. Thus 0<=u,vq<=x/2<x. This proves that every canonical refutation witness satisfies the newly tightened quotient ranges; it is not merely an upper-bound heuristic.

Choose N=B^x, then choose the CRT representatives at the same precision N^2. Ordinary positive representatives can be chosen with 0<a_i<=2N^2 and prescribed parity. For the dominant a representative, take its least nonnegative residue a0 in [0,N^2) and choose a=a0+2N^2 or a0+3N^2 with parity opposite b. Then 2N^2<=a<4N^2. The literal constructors I(a,b)=2((a+b)^2+a), A(a,b)=2((a+b)^2+3a+4b+3), and the even outer codes give

    h>=I(a,b)>=2a^2,       h=1+a+b modulo 2.

These identities are documented in the copied, hash-bound `constructor_sources/shell_source.py` and `constructor_sources/build_derived_label_range.py`. Thus h is even and dominates every other requested index. All fixed front indices lie below N^2: x,t,y+1 follow from the endpoint bound and N=B^x; F^2+t<N^2 follows from F=t!>=t, B>=F+1 and x>=2: already B^2>F^2+t, and N^2=B^(2x)>B^2. The remaining representatives are below 4N^2, whereas h>=8N^4. The full squared-cap slack, canonical frame and odd-auxiliary CRT construction from `PROOF_315.md` therefore apply verbatim. The complete eighteen-request power interface has fresh valid witnesses at these semantic values.

## Sparse coordinate residues

The sparse endpoint replaces pooled squared-error divisibilities by individual rows

    x_i-1=(A-1)s_i,       y_i-k_i=(A-1)r_i

for all fourteen pairs, including the anchor. The small abscissa residue has absolute value at most two, and the small ordinate-index residue has absolute value below 2W. Both are below |A-1|. Thus they vanish individually and give the same canonical signed-index conclusion. Conversely each canonical pair has the required integer quotients. No scalar sign graph is reintroduced. All other proof stages are unchanged.

## Conclusion and verification boundary

Soundness recovers a semantic front over nonnegative actual representatives and decodes a finite refutation. Completeness builds witnesses from any finite refutation with the strict beta ranges and the chosen even dominant semantic anchor. Composing these directions with the inherited C222/ZFC-refutation calibration proves, in ZFC, that each displayed quartic has no integer zero exactly when Con(ZFC).

The source, guarded source, factorization certificate, integral monic projection, translation and full quartic are all materialized. Normal and -O independent checks verify the complete finite identities and metrics; separate mathematical review checks the ordinary unbounded proof. No global minimum, new formal endpoint, or consistency proof is asserted.
