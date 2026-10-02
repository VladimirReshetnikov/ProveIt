# Rank five ULC with arbitrary two-by-three core and complete exteriors

Status: proposed computer-assisted extension, independent audit pending. All earlier frozen packages are unchanged.

## Theorem

Let G be bipartite with disjoint shores P union X and Q union Y, with |P|=2 and |Q|=3. Its edges are

    H union (P x Y) union (X x Q),

where H is ANY subset of P x Q and X,Y are arbitrary finite sets. Give every vertex an independent nonnegative activity. Count each feasible pair of equal-sized endpoint subsets once. The resulting support polynomial is ULC at its actual surviving degree. If that degree is five, all four Newton inequalities are strict.

The exterior blocks must be complete. Missing exterior edges, arbitrary directed orientations, and general rank-five graphs remain outside the theorem. No population bound is imposed.

## Exact support formula

Use the already approved Boolean formula from CORE_KERNEL_AND_LAST_GAP.md. A size-k support selecting I subset P and J subset Q is feasible exactly when

    0 <= |I|+|J|-k <= nu(H[I,J]).

Its exterior selection sizes are k-|I| and k-|J|. Hence its coefficient is the sum of

    u_I v_J e_(k-|I|)(X) e_(k-|J|)(Y)

over I,J satisfying that Boolean condition, with out-of-range elementary sums zero. This counts endpoint supports, not core matching witnesses. It is an ordinary all-population identity.

The five physical core vertices form a cover. If the surviving degree is at most four, delete zero-activity vertices and apply the already approved arbitrary-weight bipartite rank-four theorem. In degree five both P activities and all three Q activities are positive, and X,Y have at least three and two positive vertices, respectively.

## Normalize the exterior first moments

Divide left activities by e_1(X) and right activities by e_1(Y). This multiplies the size-k coefficient by a positive common k-th power and preserves all Newton signs. Now e_1(X)=e_1(Y)=1. Write

    M=e_2(X), N=e_3(X), S=e_2(Y).

The core activities u0,u1,q0,q1,q2 remain arbitrary positive numbers. The elementary identities in the approved complete-block theorem give

    0 < 2M < 1,  0 < 2S < 1,  0 < 3N/(2M^2) < 1.               (1)

Strictness follows from positive sums of activity squares, and from

    2e_2(X)^2-3e_1(X)e_3(X)
    =2 sum_(i<j) x_i^2 x_j^2
      +sum_(i<j<k)x_i x_j x_k(x_i+x_j+x_k)>0.

Consequently there are positive V,W,Z such that

    M=V/[2(1+V)],
    S=W/[2(1+W)],
    N=V^2 Z/[6(1+V)^2(1+Z)].                                  (2)

Explicitly, V=2M/(1-2M), W=2S/(1-2S), and Z=z/(1-z), where z=3N/(2M^2). Thus the rational substitutions cover every finite positive degree-five instance.

## The two middle gaps as finite polynomial identities

Let g_0,...,g_5 be the normalized coefficients reconstructed by the Boolean formula, as polynomials in

    (u0,u1,q0,q1,q2,M,N,S).

The first middle gap is g_2^2-2g_1g_3. The coefficient of N in g_3 is always E=q0 q1 q2, while g_1 and g_2 are independent of N. It follows that this gap is nonincreasing in N. The bound N<=2M^2/3 therefore reduces it to the smaller boundary expression obtained by substituting

    M=V/[2(1+V)], S=W/[2(1+W)], N=V^2/[6(1+V)^2].

Multiply this boundary gap by (1+V)^2(1+W)^2 to get the exact polynomial P_(H,2).

For the second middle gap g_3^2-2g_2g_4, use the exact substitutions (2) without a boundary replacement. Multiplication by

    (1+V)^4(1+W)^2(1+Z)^2

gives the exact polynomial P_(H,3). Both denominator multipliers are strictly positive. All target polynomials have rational coefficients in the variable order

    x=(u0,u1,q0,q1,q2,V,W,Z).                                  (3)

P_(H,2) is independent of Z.

## Finite core coverage

Encode H by a six-bit integer with bit 3i+j indicating edge P_i Q_j. The group S_2 x S_3 acts by independent row and column permutations. Taking the least bit mask in each orbit gives exactly thirteen representatives:

    0,1,3,7,9,10,11,14,15,27,29,31,63.

The replay enumerates all 64 labeled masks, computes their full orbits, and verifies exact coverage and no omitted representative. Since the five core activities are independent variables and the exterior blocks are universal, relabeling only permutes these activity variables. It is therefore sufficient to certify two polynomials for each representative.

## Exact certificates and strictness

For each of the 26 targets the file core_MASK_gap_K.json supplies an exact identity of the form

    P_(H,k)(x) = sum_l lambda_l x^(m_l)
                  (r_l x^(a_l)-x^(b_l))^2 + R_(H,k)(x),        (4)

where lambda_l and r_l are positive rational numbers, all exponent vectors are nonnegative integers, and every coefficient of R_(H,k) is nonnegative. The remainder is NOT trusted as supplied data: it is reconstructed by subtracting every expanded square from the complete target polynomial, including monomials absent from the original target.

Every remainder is nonzero. Since all eight variables in (3) are positive in degree five, it evaluates strictly positively. Thus both middle inequalities are strict. The first middle conclusion transfers from its boundary expression back to the actual N by monotonicity.

The 26 files contain 915 binomial-square terms in total. Exact reconstruction yields 33,318 positive remainder terms across the 26 targets. The solver-free rational replay verifies every identity, every sign, all exponents, complete orbit coverage, and nonempty remainders. Its receipt is core_exact_replay.json.

A floating-point linear program was used only to discover candidate square combinations. All accepted coefficients were reconstructed as rational numbers and checked by exact subtraction. Neither numerical solver success nor sampled activity tests enter the proof. The replay script uses Python's standard library only and does not run an optimizer.

## First and last gaps

The universal compatibility-graph proof gives gamma_2<=2 gamma_1^2/5 at degree five. The complete exterior block P x Y contains a positive K_(2,2), so its support has two positive matching witnesses. Thus the witness upper bound is strict, proving gamma_1^2>(5/2)gamma_2 for every H.

If H is nonempty, gamma_4 and gamma_5 are identical to those of the complete internal core, whereas gamma_3 is no larger. The independently approved complete-block strict last-gap theorem therefore gives

    4 gamma_4^2-10 gamma_3 gamma_5>0.

For completeness, the empty core has an equally direct last-gap proof. With the unnormalized elementary sums A,B,C,D,E,L,M,N,R,S from the complete-block theorem, put

    x=AN/(BM), y=DS/(ER), b=B/A^2,
    c=CE/D^2, h=LN/M^2, s=S/R^2.

The empty-core coefficients yield

 [4 gamma_4^2-10 gamma_3 gamma_5]/(B^2 E^2 M^2 R^2)
    =4(x+y)^2-10[xy+ch y^2+bs x^2]
    >=(x-y)^2+(7/4)x^2+(7/9)y^2>0,

using b<=1/4,c<=1/3,h<=2/3,s<=1/2. All denominators and x,y are positive at degree five.

Together these ordinary first/last arguments and the exact middle certificates prove all four strict order-five Newton inequalities. The positive matching supplies positive submatching supports. The rank-four input supplies correct normalization after every degree drop.

## Reproducibility and review status

Run `python3 replay_core_certificates.py` with assertions enabled from a directory containing that script and all 26 core_MASK_gap_K.json files. It reconstructs the Boolean kernels and target polynomials without SymPy or an optimizer, expands every rational square, and writes core_exact_replay.json. The initial exact replay passed all 26 targets in about one third of a second.

The certificate finder probe_core_certificates.py is exploratory discovery code and is not a proof dependency. The frozen complete-core package and the earlier rank-four package are unchanged. The prior star-core real-stability theorem is a separate stronger conclusion for 18 masks and is not needed to justify the middle-gap certificates.
