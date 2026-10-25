# Independent review: thirteen integers, degree 156, 127 gates

## Verdict and frozen result

PASS. The final pointwise-optimized equation has thirteen unrestricted integer variables, exact total degree156, and127 live binary gates:75 multiplication,27 addition,25 subtraction. Its SHA-256 is 30d59306923e21d8eeb30ba02903a3ff895fd9aaf3a40ad873dc31977505ba22.

The earlier128-gate form was also reviewed, but is not the final reported cost. The change introduced Ds=Delta I², Fs=1+Ds and Q=Delta Ds to avoid subtracting1 from Fs. It is a literal identity, with no change in zero set, degree or coefficient tuple. The final127-gate form has been rechecked normally and with Python optimization.

## Norm identity and conjunction

Independently multiplying all eight signed-root factors gives

[(x²-g-d-f)²-4(gd+gf+df)]²-64gdf x².

The substitution x²=carrier+db, g=ga, d=db, f=fc gives the displayed centered schedule exactly. Since U is nonzero, dividing by U^8 gives the three-root carrier rho=±sqrt(G)±2sqrt(Dt)±4sqrt(Fs). N is a square modulo4, hence N cannot equal -2. Thus (N+1)(auxiliary+1)=1 holds exactly when N=auxiliary=0. This is valid for arbitrary signed residuals.

## Unconditional realness and complete squareclass proof

The proof establishes q even nonzero, H odd nonzero, and U=2q³H nonzero without any Pell or budget conclusion. Since |X|>=8 and a=(X+1)Y, either a=0 or |a|>=7, implying Delta=(a+2)²-1>=3 and Fs=1+Delta I²>=1. Also Dt=1+XY²(XY²+1)k² is positive and odd. G=1 mod4 is odd and nonzero. If G<0, its radical is the sole nonzero imaginary term in every signed factor, so no factor vanishes. Hence N=0 forces G>0.

Write G=u1²d1, Dt=u2²d2 and Fs=u3²d3 with positive squarefree di. The first two ui and di are odd. A vanishing factor makes the signed rational sum of coefficients u1,2u2,4u3 times their squarefree radicals rational. Distinct squarefree radicals, including1, are linearly independent over Q; this follows from character projection in the multiquadratic extension of the finitely many involved primes.

For a common nontrivial squareclass, a group containing G has one odd coefficient and all others even, so cannot sum to zero. Without G, a group containing Dt has one coefficient of exact valuation1 and its only possible companion divisible by4, so cannot sum to zero. The remaining possibility is a single nonzero Fs term. In an even squareclass, only Fs can occur, also impossible. Therefore every squareclass is1 and all three roots are integers. This argument explicitly allows Fs even and shared squareclasses; neither pairwise distinct radicands nor numerical root magnitude separation is assumed.

This establishes the key extraction on every integer zero, not merely on the canonical source family. The finite parity diagnostics are not being substituted for this unbounded squareclass argument.

## Both every-zero coordinate maps

Take signed roots g,tau,f from a vanishing factor, so rho=g+2tau+4f. Since G is odd, g is odd. Set

f_old=f, p3_old=(g-1)/2, n_old=n-g-4f.

Then Z_old/U=2tau-(2L+k), restoring the old first carrier exactly. The new Fs equals f_old², so both the old strong row and the old auxiliary definitions are restored. Finally p3_old(p3_old+1)=(G-1)/4 makes the old positivity equation exactly budget=1+p1²+p2²+p3_old(p3_old+1). Every new zero therefore yields a literal zero of the pinned fifteen-variable source.

Conversely, for any old zero, retain shared coordinates, delete f and p3, and set n_new=n_old+(2p3_old+1)+4f_old. The old carrier supplies the integral signed root tau, the old guard gives G=(2p3_old+1)², and the old strong equation gives Fs=f_old². One signed norm factor vanishes and auxiliary is unchanged. This proves the complete reverse map on every old zero. Canonical completeness is inherited by composition and requires no new rank-tuning, guard-representation theorem or strong-pair interpolation.

## Exact independent finite checks

../../independent_norm_audit.py was written independently of the producer builder/audit. It checks every arithmetic gate by exact polynomial identities, requires all gates to be bound, checks topology and full liveness, verifies the complete eight-factor norm and centered substitution, verifies the signed lift, and uses a separate graded-lex leading computation. All127 actual live-gate operation mutations are rejected in each Python mode.

The attained coefficient at j^106 w^14 v^14 z^9 r^4 c^8 y is exactly +2^171 3^120 beta^106. The exponent sum is156. Every gate's selected leader is nonzero, and the authentic beta is explicitly authenticated; this is stronger than a random-ray or symbolic-generic degree estimate. INDEPENDENT_NORMAL.json and INDEPENDENT_OPTIMIZED.json bind these results to the final equation hash.

The inherited ordinary Source34-to-K215-to-refutation calibration and its exact six coefficient payloads are unchanged. These tests and the new proof do not create an encoded object-language ZFC derivation, a new end-to-end kernel certificate, or an optimality result. The point trades fewer variables for higher degree and more gates than14Z88/119 and15Z44/111; it does not dominate those tradeoffs.
