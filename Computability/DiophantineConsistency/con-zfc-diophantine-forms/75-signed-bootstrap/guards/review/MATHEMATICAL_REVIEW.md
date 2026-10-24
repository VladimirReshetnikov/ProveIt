# Independent review of signed34

Verdict: the new signed-X bootstrap is mathematically sound relative to the explicitly inherited ordinary Pell classification/strong-rank/signed-auxiliary lemmas and the source34 native compiler calibration. It is not a newly kernel-checked theorem. Literal checks independently pass, with hashes in CHECK.json.

## Rank bootstrap

Q>=16 and Q(Q²−1)<R<Q⁴−2 come entirely from the unchanged same-sign F,alpha,C guards and coherent masks. X=4qu² gives either X=0 or signX=signq and |X|>=4Q. X=0 is excluded by the main norm modulo H=4a+3; here a=Y, |Y|>=Q³. Thus |E|>=4Q⁴>3R+1 and B=|a+2|>R, independent of either sign X.

The same-sign eta,zeta guard yields k nonzero and k0(Z0−1)<c0<k0(Z0+1), so c0>k0. Classification of the consecutive-product equation for negative X uses −XY²−1>0, genuinely giving P0=|2XY²+1|. P0>B and monotonicity give p>n. Modulo |E|, P0 is +1 for positive X and −1 for negative X, explaining the parity factor (−1)^(n−1) in epsilon. The resulting congruence2n=epsilon(R+1) gives either n>R or n>=(R+1)/2; it does not assume an index parity prematurely.

For both branches p is large, c0>B(B²−1)² and c0>2p,2R. The inherited ordinary strong theorem therefore gives c0|m and m>2p. The signed auxiliary proof uses c² and modulus|c|, so changing the sign of c or A does not affect its conclusion R=±p mod c0. The two numbers lie strictly inside(0,c0/2), whence p=R. Epsilon−1 contradicts p>n>R. For epsilon+1,2n<2R<|E| andR+1<|E| imply literal2n=R+1. This is the valid point at which R becomes odd.

## Negative-X exclusion

Write x=|X|,Z0=|Y|,r0=(R−1)/2. Recurrence bounds give c0/k0 >= (2B−1)^(2r0)/(2(2P0)^r0). The strict base inequality in PROOF.md gives c0/k0>(x−3)^r0/2. It holds universally for x>=64,Z0>=5: substitution x=64+v,Z0=5+w turns its difference into

4v w²+20v w+2v+260w²+1340w+347,

a polynomial with strictly positive coefficients. Hence Z0>(x−3)^r0/2−1>2^(2r0+1)=2^R. The latter estimate follows from61^r>4^(r+1)+2 for r>=1, proved by induction from61>18 (multiplication by61 dominates multiplication by4).

The H estimates then place x2^R and x+2^R strictly below|H|. Since R is odd, psi_A(R)=psi_|A|(R), whereas chi_A(R)=sign(A)chi_|A|(R). Combining the two possible D signs with sigma=sign(c) gives precisely sigmaX=2^R or sigmaX2^R=−1 modulo H. The inverse branch cannot hit−1 because1<x2^R<|H|−1. In the direct branch the difference has absolute value<|H|, giving sigmaX=2^R, hence x=2^R. No sign of c was silently fixed.

Because q|X and signq=signX, negative X implies q=−2^t. The Mersenne congruence q=1 mod(2^d−1),d>=3 rules this out by reducing t modulo d. This elementary lemma applies to all t, not merely tested examples.

## Positive branch and transport

After X>0,epsilon=sign(k)=+1, hence eta,zeta>0. The positive-X signed-Y proof of PROOF44 applies with the stronger boundX>=4Q, giving Y>0 andX=2^R. That inherited argument only used its old twice-square guard to establish X>0; its subsequent quantitative inputs remain present here.

The cleared transport modulo q givesZ=0 modq, becauseq|X andq−1=−1 modq. Therefore z_old=Z/q is integral and division recovers the literal Q41 transport. Setw_scale_old=u² andu_old=2^((R−1)/2). These assignments restore all Q41 equations exactly. No quotient positivity is required in this unrestricted-domain restoration.

Conversely canonical source witnesses have q=2^t,t odd,R odd,R>3q. ThereforeR−t−2 is even and nonnegative; u=2^((R−t−2)/2) andZ=qz_old restore the new guard and transport. This uses canonical completeness, not a false bijection with every Q41 zero.

## Exact algebra

check_independent.py locates changed Q41 rows by their formulas, reconstructs signed40 without importing the builder, verifies cleared transport modulo the new guard, substitutes all six sextic restorations including the root shear, and recovers all19 signed34 rows. All34 unknowns are distinct. Every residual has degree<=3 and the full symbolic SOS has coefficient4 at r²c⁴, so specialization of fixed ports cannot lower degree6.

Conclusion:34 unrestricted variables and19 cubic-or-lower residuals, one exact sextic, is supported by the reviewed ordinary proof and independent exact identities. No improvement to quartic41 or octic30 follows. The novelty supported here is removal of a genuine scale coordinate via signed-power bootstrap/transport absorption, not merely a different monic elimination.
