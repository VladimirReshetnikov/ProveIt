# A quadratic-character obstruction on an infinite genuine subfamily

Proposed extension to the frozen all-but-main-projection theorem, 3 October 2026.

Fix the theorem's explicit q=B^(2x+2), so q is an even square. Put Y=q^3, h0=4q^3+3 and Dthin=4h0. Restrict its progression parameter to r=Dthin*j, with j a positive integer. Then

w=1+(q-1)Dthin*j, X=q^3*w, H=4q^6*w+h0.

Both w and H are odd; w is 1 modulo 4h0, H is 3 modulo 8, gcd(w,H)=gcd(w,h0)=1, and gcd(q,H)=1. Since q^3 is a square, Jacobi symbols satisfy

(X/H)=(w/H)=(H/w)=(h0/w)=(w/h0)=1.

The first and second reciprocity swaps introduce no sign because w is 1 modulo 4. The last equality uses w=1 modulo h0. These are Jacobi reciprocity identities for positive odd coprime denominators, with no primality hypothesis.

Every main index selected by the parent theorem is odd. The supplementary law for 2 gives (2/H)=-1 because H=3 modulo 8, hence (2^p/H)=-1. Therefore 2^p is never congruent to X modulo H on this thinned progression for any odd p. In particular the parent theorem's canonical residue satisfies 1<=r_main<H.

The shrinking-target existence argument survives this fixed thinning. Set g_thin(j)=g(Dthin*j). Its controlled curvature is

g_thin''(j)=-Kstar*Dthin/[j(log j)^2]*(1+O(1/log j)),

since Dthin is fixed before j tends to infinity. Thus the same second-derivative and Erdos-Turan estimates hold on N<=j<2N, with constants depending on fixed Dthin. Use target interval [0,kappa0/log(2Dthin*N)). For sufficiently large N, its expected count minus discrepancy is at least kappa0*N/[2log(2Dthin*N)], which is at least delta0*N/[32L0*log N] because log(2Dthin*N)<=2log N eventually and kappa0=delta0/(8L0). Each selected j gives the exact Pell-ratio and every other parent condition via the unchanged interior-margin argument with r=Dthin*j.

Consequently every genuine compiler/input has infinitely many fully positive raw tuples satisfying every comparison except its main projection, with exact strictly positive SOS value r_main^2. The positive21 tuples likewise satisfy every comparison except the main norm, with strictly positive SOS value [r_main(2D-r_main)]^2 (D here denotes the Pell root, not Dthin). This establishes genuine nonredundancy of those comparisons in their respective children.

This does not construct a full zero or establish global restored-index positivity. It rules out only the specified infinite subfamily. No full enormous candidate is numerically materialized by this argument.

This is a new extension, not a retrospective change to the frozen parent packet's evidence status. Await independent review before publication.
