# Independent review of the frozen ten-positive branch

## Verdict

**PASS at the explicitly inherited ordinary source/native calibration.** I found no new algebraic, positive-domain, transport-sign, completeness, coefficient-binding, operation-count, or exact-degree defect in either construction. The two results are ten-positive equations at **81 operations / degree 750** and **82 operations / degree 560**. They are operation/degree tradeoffs, not variable reductions, consistency proofs, global minima, or new internal formal proof endpoints.

This review is independent of the producer: `independent_check.py` neither imports nor executes `positive/build.py` or `positive/verify.py`. It reads the frozen graphs and coefficient/source data, derives an independently written exact algebra specification, and reconstructs the complete literal coefficient tuple from the printed finite decoder. No producer file was modified and no remote write was made.

## 1. The potentially unsafe inverse shear is not used

The universally valid substitution is Y_old=q^3 s and n_old=n−s. The latter need not be positive. The proof explicitly says so and does not infer new soundness from old positive-domain soundness.

The new numerator and denominator are independently certified to satisfy Z_old=q^3 Z and M_old=q^3 M. Because this finalizer is quadratic in the cleared coordinates, the exact output relation is N_old=q^6 N, not q^12 N. My checker proves these as polynomial identities in free indeterminates, and rejects both the wrong exponent and wrong shear sign. These are not positive-input or modular sample tests.

The old and new graphs have exactly the same kernel after Y substitution. Soundness is instead established directly for the actual positive n. Only after the direct sign argument do later arithmetic interfaces need the shifted coordinate, and they use it merely as an integer addend.

## 2. Root recovery and the order of dependencies

For positive inputs, Y>0, H,M>0, E>1, U>=c^2, Fsq>c+1 and Q>1. For integral b, either V=−c or |V|>=Fsq−c>1, so Dy=QV^2−1 is positive before the sign of b or B is known.

The exact identities Fsq=(1+2a)^2 and Q=4 Delta^2 U^2 G imply that both Q−1 and Dy are −1 modulo G. At a zero, (Q−1)(Z/M)^2=G Dy. Prime valuations at every divisor of G therefore force G to be square. This works for a rational Z/M and does not require gcd(M,G)=1. Since gcd(E,F0)=1, E and F0 are separately positive squares.

The rational adjacent-Pell descent is valid. In reduced y=r/m, the norm implies m^2 divides Q−1. Its linear transform has integral first coordinate and preserves the denominator of the second because 2Q−1 is 1 modulo m. The strict bounds v<y<Qv/(Q−1) give −v<v'<v, and norm one excludes v'=0. Descent terminates at v=y=1. Thus y is integral and Z/M=epsilon*g*y for either sign epsilon.

The doubled pair f=1+2a, I=2Ug satisfies f^2−Delta I^2=1, Q=(Delta I)^2 and c^2|I. Consequently the retained all-index folding interface has its original hypotheses. The first-index exclusion yields k>=8V0+4 and c>X; the mask bound yields b>c and V>0. These do not depend on B>=0, q parity, carrier divisibility, native decoding, or n−s positivity.

## 3. Both root signs are covered by direct transport

The carrier is exactly

    Z/M = n + kappa − (1+hL) B/h − rho.

The one-sided bound rho<b/mu^2 follows from b−e=c(T+alpha)−k+1>0. No nonnegativity of rho is needed.

For L=V^2, a^2>G gives g<a; then V>(Fsq−1)b>ab>3g and y/V<3/2. Hence gy<V^2/2. If the actual integer B<=−1, (1+hL)B/h<=−V^2−1/h. For either epsilon,

    n < V^2/2 − V^2 + V/mu^2 < 0.

For L=bV, odd folded p and c>=3 give p>=3 and c>=4Delta+3, hence V>4Q. With Q=S^2, the positive auxiliary trace index is odd; indices 1 and 3 would give V=1 and V=4Q−3. Thus it is at least 5 and V>=16Q^2−20Q+5>8Q^2. This yields b>4Delta^3 I^2>4g, so gy<3bV/8<L/2. For B<=−1,

    n < L/2 − L + b/mu^2 < 0.

Both contradictions use the real positive input n, not the shifted n−s. In each case the upper bound epsilon*gy<=gy handles the negative root sign as well as the positive one. Thus B>=0 and then C>0 follow without circularity.

## 4. Ordered decoding and projection remain licensed

Only after C>0 are the strong-rank and signed-index interfaces used to recover p=R. Odd p supplies q even and J odd. Only then does gcd(mu^2,hH)=1 license the carrier reduction modulo mu^2 and mu^2|e. The old first-index congruence and strict ratio bounds are now in their original order.

Reducing the integral carrier modulo H gives H|h*Kpos, because gcd(mu^2,H)=1. This implies the retained weaker premise H|q^3*h*Kpos. No arbitrary factor is cancelled modulo H. The inherited whole-product projection and strict bound apply to the entire product q^3*h*(X−2^R)*(2^R*X+1), giving X=2^R and integral kappa.

The residual fraction then gives integral Wt. Since W=1 modulo h, h|B and t>=0. The condition q^3|Y is literal in the new polynomial. Fixed-minus parity, half-binomial rounding, and fresh unscaled source reconstruction at Y(X+1)+2 therefore have the same required hypotheses. The dropped positive-domain premise on n_old is not needed at these stages.

## 5. Canonical completeness, including t=0

The retained canonical outer data supply q^3|Y before the fresh strong period is selected. This is an explicit canonical source condition, not an assertion that generic cofinality implies divisibility and not a restriction imposed on an arbitrary old zero.

Choose one seed Pell period modulo c^2*tau. Then I0 is divisible by c^2*tau, i=I0/(c^2*tau)>0, U=I0/tau, a=Delta I0^2, and F0=f0^2. Doubling this same seed produces the actual f,I and literal Fsq,Q. There is no unsupported simultaneous choice of unrelated Pell solutions.

The inherited auxiliary converse applies to the doubled strong pair: its hypotheses do not prescribe parity of the strong index or of I/c^2. It supplies the positive actual T and V,y. With canonical integer kappa,rho,t, choose

    n = g*y + W*t + rho − kappa.

Seed growth gives g>kappa, and rho,t>=0, so n>0 even when t=0. Equivalently the already positive old n_old becomes n=n_old+Y/q^3. The universal q^6 identity completes the converse. All ten coordinates are strictly positive.

## 6. Whole indexed coefficient tuple

The independent checker does more than compare byte hashes. It decodes the complete printed 436-character base-62 seed; rebuilds all 430 actions; constructs all 943 distinct, directly indexed tiles; verifies Start0, Forbidden1 and the literal renamed initializer target; reconstructs all selector/copy/anchor coefficients and the 986-position support; and computes beta,K0,MC,MF from the printed formulas.

Every independently reconstructed integer exactly equals its decompressed literal file, has the stated bit length, and has canonical unsigned little-endian encoding. Both graph bindings are the entire source133 tuple. The checker separately confirms the native mask populations and low bits and the new DC-dependent controller unit triples, including H0 residues **23, 3359, 404489**. MF_native is recovered as MF−beta, so the source shift is applied exactly once. No K from the differently calibrated q-cube graph is imported.

All listed frozen manifest files and retained source-file pins are checked. The copied source/native proof explicitly rebuilds the coherent indexed tuple and fresh packed witnesses rather than asserting pointwise equality with a differently ordered native encoding.

The deeper all-index folding, rank, projection-height, native tiling and machine/refutation calibration theorems remain the expressly inherited ordinary contracts. This audit checks their invocation and the new composition, not a new Lean or object-ZFC derivation of that entire transitive development. In particular the source's full aggregate carry theorem and blank-machine calibration are not replaced by finite experiments.

## 7. Exact identities, counts and full homogeneous certificates

Every one of the 81 and 82 actual new gates and 84 and 85 copied parent gates is checked against independently written polynomial interfaces. Verified semantic cutpoints are treated as fresh indeterminates only after their definitions have been certified. Substitution induction therefore proves equality of the full multivariate circuit polynomials; it is not a fingerprint/ray heuristic. The separate free-polynomial carrier/finalizer checks bind these complete graphs to the normalization identity.

All gates, ten unknowns and four ports are live. The literal cost splits are (48 products,19 sums,14 differences) and (49,19,14), including scalar multiplications.

A separate exact highest-homogeneous replay propagates all ten input degrees as one and treats beta,K0,MC,MF as coefficient parameters. It certifies the full forms

    [N81]_750 = 2^14 (beta J)^506 w^46 s^108 i^20
                 (eta+zeta)^64 (T+alpha)^4 (beta J−F−alpha)^2,
    [N82]_560 = −2^10 (beta J)^384 w^34 s^80 i^14
                 (eta+zeta)^46 (T+alpha)^2.

Exact coefficient extraction gives respectively 2^14 beta^506 at J^506 w^46 s^108 i^20 eta^64 T^4 F^2 and −2^10 beta^384 at J^384 w^34 s^80 i^14 eta^46 T^2. Actual beta>0 proves attainment after specialization. This is a complete homogeneous-form certificate, not a modular ray or generic-port-only assertion.

The checker independently corrupts the operation in **every actual gate**, producing 163 rejected gate mutants, and also rejects 12 targeted operand/sign corruptions and the two wrong scaling/shear controls. No `assert` is used for required checks.

## Reproduction

Requires the already installed Sympy 1.14.0 for exact polynomial normalization; everything else is Python standard library.

    python -B review/positive/independent_check.py > review/positive/CHECK_NORMAL.json
    python -B -O review/positive/independent_check.py > review/positive/CHECK_OPTIMIZED.json
    cmp review/positive/CHECK_NORMAL.json review/positive/CHECK_OPTIMIZED.json

Run these commands from the packet root. The checker locates the frozen positive branch relative to its own file. The two reports must be byte-identical. Finite certificates supplement the unbounded proof review above and do not decide consistency.
