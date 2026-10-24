# Exact norm sharing and a translation lower bound

## Result and comparison

These four literal ordinary polynomials have ten unrestricted integer unknowns, the same twelve actual fixed integer leaves as the pinned short-guard parent, and exactly its corresponding polynomial values. The new work changes only the arithmetic graph. It introduces no additional mathematical premise into the consistency equivalence.

| Variant | Latest pinned parent operations | Here | Exact degree |
| --- | ---: | ---: | ---: |
| polar | 471 | 467 | 1245324 |
| linear | 475 | 470 | 1179788 |
| cubic | 478 | 473 | 1114252 |
| sixterm | 512 | 507 | 1080888 |

The current comparison is ProveIt commit 7e533c33819ee1f703b69f2778a767cdc069940d, not the older incoming package. The 23-integer degree-ten and 20-integer degree-eighteen constructions in those packages are prior results, not new contributions here. No new lower-degree integer-coordinate chart was established in this component.

The exact graphs are integer10_*.json. Reading a fixed integer leaf or reusing a node costs zero; every live binary addition, subtraction, multiplication, square, and scalar multiplication costs one. These are description-circuit improvements, not new variable counts or degrees, and not claims of globally minimal circuits.

The second result is a rigorous limitation of the existing route: degree 1080888 is the minimum among all polynomial translations of the final coordinate with the short-guard prefix fixed. This includes translations with arbitrary real polynomial coefficients, hence in particular all integral polynomial shears. It is not a lower bound on other norm carriers, source encodings, coordinate changes involving other variables, or arbitrary ten-variable equations.

## Exact complete equation

The variables, in order, are t,g0,c0,k0,l,w,x,y,z,m. The complete source-to-output arithmetic graphs and twelve fixed numeral payloads are included. The fixed source data, compiler calibration, generalized Pell/Lucas reliability, interpolation argument, and canonical short-guard proof are inherited from source/BASELINE_PROOF.md, source/PROOF.md, and source/SHORT_GUARD_PROOF.tex. Their content is mathematical; no new kernel-checked or object-language consistency derivation is supplied.

Write the unchanged short-guard registers as

    Delta = g(cap-g) K^2 - cap^2(C-KL)^2,
    r = bQ,
    a0 = r + (9Delta-3)(rz)^2,
    a1 = DFI,
    Sigma = xi S^5,
    Theta = (rho^3-rho S^2-S^3)(rho^2+23S^2).

For R depending on the other nine variables, put Z=Sigma(m+R)-Theta. The equation is

    [Z^2+Sigma^2(a0-a1)]^2 - 4Sigma^2 a0 Z^2 = 0.

For the polar choice R=0. For linear and cubic respectively,

    R = 2AEGH,
    R = 2AE0(D-2C^2)GH.

For sixterm set h=halfA, u=C^2, E0=u xi and

    qa = u(2h^2-11)+6,
    qb = u^2(8h^4-52h^2+143)+u(32h^2-176)+48,
    T6 = xi(B1-C)qa+16E0 xi y qb+3y,
    R = 32768 u^3 E0^4 h^9 [(h-1)T6-2y].

This is exactly the previously published six-term shift, since E0=C^2 xi; the new factorization merely reuses E0. Every abbreviation in this text is fully inlined by the supplied graph. None is another quantified coordinate. All exponents are fixed natural numbers. The graphs contain only integer leaves and binary +,-,*.

The polarized norm is identically

    [Z^2-Sigma^2(a0+a1)]^2 - 4Sigma^4 a0 a1.

For each of the four displayed integral shifts R, m -> m+R is an invertible integral polynomial coordinate translation. Consequently the unchanged prior proof gives the same existential equivalence to a finite ZFC refutation, and negation gives the ordinary ZFC-provable equivalence of no integer zero with Con(ZFC). This does not assert either side, decide consistency, or replace the inherited unbounded calibration by finite tests.

## The exact graph identities

The following identities hold in the polynomial ring over the integers, with no nonzero or sign premises.

1. The source has tc=tc_original-2. Thus

       X = nn(sc+tc+1)-sc-1
         = nn(sc+tc_original-1)-sc-1.

   The explicit tc subtraction no longer needs a live gate. Let Xp1 denote the already computed nn(sc+tc_original-1)-sc.

2. The source K=X+1+twice_k(Phalf-1) becomes

       K=Xp1+twice_k(Phalf-1).

   This reuses Xp1 rather than computing X+1 again.

3. Since F=Fm1+1,

       G=(h-1)Fm1-1=h Fm1-F.

   This saves one operation unless h-1 remains independently necessary, as it does in the six-term shift.

4. Compute S2=S*S, S3=S*S2, and S5=S2*S3. Both Sigma and Theta use this same S3. No separate S4 gate is needed.

5. In the linear and cubic shifts compute GH=G*H and use

       I=(GH)^2-H^2+1.

   This equals (G^2-1)H^2+1 and makes GH available to R without its extra final multiplication. It saves one operation jointly, not in I considered alone.

6. In the six-term shift use

       u^7 xi^4 = u^3 E0^4,
       u xi^2 = E0 xi.

   These two shared-register factorizations remove two further multiplications. Together with (1), (2), and (4), they account for five operations saved. For the linear and cubic forms, (1)--(5) account for their five savings. For polar, (1)--(4) account for four.

The verifier compares every common source register at exact symbolic cut points, then compares the complete shear and final norm. Therefore it verifies equality of the complete polynomial, not only equality on zeros or agreement at random inputs.

## Exact degrees

The unchanged source weights are

    deg(h)=16384, deg(B1)=7942, deg(C)=1, deg(xi)=2, deg(y)=1,
    deg(Sigma)=81922, deg(a0)=294382, deg(a1)=458818.

Exact coefficient expansion in the five abstract source registers gives weighted degrees of a1-R^2 equal to 426050, 393282, and 368449 for linear, cubic, and sixterm. This is independently recomputed by check.py, rather than accepted from the delivered graph's naive bound.

For linear and cubic the squared defect is dominant. Their degrees are 4*81922+2*426050=1179788 and 4*81922+2*393282=1114252. In sixterm the squared inner term has degree at most 1064586, while the cross term has exact degree

    4*81922+294382+458818=1080888.

For polar the dominant term Sigma^4 a1^2 has degree 1245324. Nonzero leading coefficients modulo three primes are calculated using the actual supplied fixed numeral payloads. They verify attainment of the displayed degrees after specialization. The naive DAG degree_upper_bound remains 1245324 for the sheared forms; it is not falsely relabeled as the attained degree.

## Why no final-coordinate polynomial translation can do better

For a nonzero polynomial P let P_top denote its highest homogeneous part. All source registers below are independent of m. Put

    U0 = 3 cap_top K_top L_top r_top z,
    V0 = (2 A E G H)_top.

Both U0 and V0 are nonzero polynomials. The short guard is dominated by its negative approximation square, so

    (a0)_top = -U0^2.

Indeed C has degree one, KL has much higher degree, and cap^2(C-KL)^2 strictly dominates g(cap-g)K^2; its leading part is cap_top^2 K_top^2 L_top^2. Multiplication by 9(rz)^2 yields the asserted negative square. The other terms in a0 have strictly smaller degrees.

The elementary leading parts of D,F,I also give

    (a1)_top = V0^2.

Equivalently, the linear shift has degree 229409 and its defect has strictly smaller degree than a1=458818, so a1 and (2AEGH)^2 have identical highest homogeneous parts. The latter fact is proved by the exact defect computation, not assumed from a formal asymptotic expansion.

Consequently the fixed cross term in the unpolarized norm has highest homogeneous part

    (-4Sigma^4 a0 a1)_top = (2 Sigma_top^2 U0 V0)^2,

a nonzero square of degree d=1080888. Let R be any real polynomial in the first nine coordinates and let

    B_R = [Sigma(m+R)-Theta]^2-Sigma^2(a0+a1).

The translated norm is B_R^2-4Sigma^4 a0 a1. If 2deg(B_R)>d, its degree is 2deg(B_R)>d. If 2deg(B_R)<d, its degree is d. If 2deg(B_R)=d, its degree-d part is the sum of the two squares (B_R_top)^2 and (2Sigma_top^2 U0V0)^2. This cannot vanish identically over the reals: a sum of squares is the zero polynomial only when each summand is the zero polynomial. The second summand is nonzero. Thus its degree is again d.

Every such translation therefore has degree at least 1080888. The six-term equation attains the bound, proving the asserted restricted-family optimum. The older odd-degree argument for the old guard is unnecessary and would not apply here, since this new bound is even.

## Validation and boundaries

Run python build.py, python check.py, and python -O check.py. The checker imports neither build.py nor circuit.py. It authenticates all actual fixed payloads, independently reconstructs their fixed recipes, checks exact local polynomial equalities for the entire graph, expands the radical defects over the integers, verifies graph topology and backward liveness, counts all live operations, and computes nonzero degree certificates. It also performs 360 signed modular native-source replays per variant and rejects a topology-preserving final-sign mutation in each graph.

The exact polynomial identities and leading-form proof are universal arguments. Modular samples are supplemental transcription tests, not proofs of consistency or of the compiler/Pell theorem. No new low-degree frontier point, fewer-variable construction, upstream repository edit, or proof-assistant result is claimed.
