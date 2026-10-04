# Independent audit: periodic collision macros with at most four live signals

Date: 4 October 2026. Verdict: **PASS for Theorems A–C as explicitly scoped in the reviewed proof.** No substantive mathematical correction is required. The degree bound is at most four, and uniqueness is for the natural witness fiber of a supplied input encoding. Neither general signal-machine nontermination nor continuation through an accumulation is represented.

Reviewed author source: `/workspace/shared/substrate-semantics56-20261004/PROOF.md`, SHA-256 `df7cefb472a76e6f34ce7fff0b1e8548782a82f4863fac2ecd2d682c69941a77`. A byte-for-byte snapshot is retained as `reviewed-proof.md` in this directory. This audit does not modify the author's packet. The source's generic chamber-to-polynomial frontend remains a proved construction, not a claimed completed implementation.

I independently derived the scalar positivity tests, signed-spectrum reduction, private-copy and sign-trichotomy arithmetic compilers, observable clock test, and complete spectator example. I then read every section of the author's proof. Only the newly written, inspected `check_exact_algebra.py` was executed. It imports only Python's standard library and performs exact algebra. No upstream/saved program, schedule executor, or physical simulator was executed. Finite checks support the proofs below; they do not establish an all-input theorem on their own.

## 1. Exact hypotheses that make the result true

The result requires all of the following, which the reviewed source supplies:

1. A fixed finite signal machine with fixed rational velocities and number-preserving collision rules
2. Standard collision input and output sets with pairwise distinct speeds within each set
3. A fixed outgoing collision section, with output order inside a co-location group determined by increasing speed
4. A fixed, nonempty finite word of **complete simultaneous batches**, each separated from the preceding batch by strictly positive physical time
5. The final ordered labels and outgoing co-location pattern equal those of the initial section
6. At most four live signals, or separately the dimension-at-most-two section hypothesis
7. The integer/rational initial coordinates are external inputs; machine data and the word are compilation constants

“Four signals” is not “four velocities” or “four meta-signals.” The worked example uses five possible velocities but four signals at a time. “Periodic” refers to the complete combinatorial collision macro, including all simultaneous sites and all incoming signals, not to literal equality of spatial states or equal physical periods.

The theorem decides whether every finite prefix of that supplied word is actual. It neither searches over all infinite collision itineraries nor supplies event semantics at the limiting time. This distinction is essential: an additional collision at a finite macro endpoint invalidates the word, whereas an additional contact only at its accumulation limit does not invalidate any finite prefix.

## 2. Dimension and complete-chronology proof audit

### 2.1 The section dimension is genuinely at most two

With N outgoing signals, translation removes one spatial coordinate. Every co-location group of k outputs imposes k−1 independent adjacent-gap equalities. Number preservation and at least one genuine collision imply that some outgoing group has k≥2. Therefore the section dimension is

    d = N−1−sum_groups(k−1) <= N−2 <= 2.

This is an ambient linear-coordinate count, not a claim based on a plotting projection. Simultaneous binary groups at N=4 impose two zero gaps; a triple group also imposes two; a four-output group imposes three. All have no larger dimension than the generic binary-collision section. If d=0, homogeneous evolution cannot generate a positive future collision time; the claimed empty branch is correct.

An arbitrary observation cut after the collision would introduce a phase coordinate and would not satisfy this argument. The source explicitly avoids that mistake. Likewise, allowing a one-output replacement would break the implication from “collision occurred” to an outgoing zero gap; number preservation prevents it here.

### 2.2 The adjacent-pair chamber really certifies all collisions

At a legal outgoing section, a co-located pair is separating because outputs are speed-sorted and have distinct speeds. For an adjacent gap g_i and closing rate c_i=v_i−v_(i+1), the collision-free continuation is g_i−c_i tau. A closing pair has c_i>0 and starts with a strictly positive gap. Every nonclosing pair stays nonnegative, and a pair born co-located separates strictly for every positive tau.

Choosing a proposed incoming closing pair j determines tau=g_j/c_j. Comparing every other closing candidate to tau has precisely three relevant effects:

- A smaller candidate rejects an omitted earlier collision
- Equality at any additional index forces its inclusion in the simultaneous batch
- Strictly larger candidates ensure separation of all other adjacent pairs at the batch

A nonadjacent encounter cannot evade these tests: before any such encounter, an intervening adjacent gap must vanish. A multiple collision is exactly a maximal consecutive zero-gap block, so all incoming signals are included. Separate zero blocks remain separated by strictly positive gaps; treating them atomically prevents omissions at remote simultaneous sites.

The distinct-speed input condition also follows geometrically for a valid positive-time meeting block: incoming positions in increasing order require strictly decreasing velocities. It is safe to reject a proposed incoming zero index whose relative closing rate is not positive. Speed ties at distinct sites are harmless and need no candidate division.

Number preservation keeps the spatial slot count fixed. At a collision, sorting the replacement outputs changes labels in the block but not its coincident positions. Thus every gap, elapsed time, and translation increment after a fixed finite word is a homogeneous rational linear form in the initial free gaps. The macro's chamber has the form E x=0, G x>0. The final section equalities are needed even if the ambient linear map does not preserve the section away from legal inputs.

The source's induction criterion

    E M^n x=0 and G M^n x>0 for all n>=0

is therefore both necessary and sufficient, with no hidden permissive tie convention. The stated loose row bound (2m+1)(N−1)+m is valid: (m+1)(N−1) section rows, at most m(N−1) candidate rows, and m positive-time rows. This is not an arithmetic-operation count.

## 3. Scalar recurrence audit, including the dangerous boundary cases

For a 2×2 rational matrix M, every observation v_n=a M^n x satisfies its order-at-most-two characteristic recurrence, even when the minimal recurrence has smaller order. Consequently equality for all n is equivalent to v_0=v_1=0. Repeated roots, scalar matrices, singular matrices, and zero observations do not require a diagonalizability assumption.

### 3.1 Nonnegative real roots

Suppose a scalar recurrence has characteristic roots alpha≥beta≥0 and starts v_0=A, v_1=B.

- alpha>beta>0: write v_n/alpha^n=D+(A−D)(beta/alpha)^n, with D=(B−beta A)/(alpha−beta). All terms are strictly positive iff A>0 and D≥0. Weak positivity changes A>0 to A≥0. Sufficiency follows because each normalized value lies between A and D, with the coefficient on A strictly positive at every finite n. Necessity of D≥0 follows from the limit. In particular D=0 is allowed under strict positivity
- alpha>beta=0: v_n=B alpha^(n−1) for n≥1. Strict positivity requires A>0 **and B>0**. Replacing the latter by B≥0 is false. Weak positivity allows both initial values to be nonnegative
- alpha=beta=lambda>0: v_n=lambda^n[A+n(B/lambda−A)]. The exact condition is A>0 and B−lambda A≥0, with A≥0 for weak positivity. This covers both Jordan and scalar cases
- alpha=beta=0: v_n=0 for n≥2. Infinite strict positivity is impossible; weak positivity is exactly A,B≥0

The author's cases match these formulas. A zero dominant coefficient, zero smaller root, repeated positive root, and nilpotent recurrence are not conflated.

### 3.2 Negative and complex roots

When M has real spectrum, B=M² has nonnegative roots. Apply the preceding classification separately to v_(2n) and v_(2n+1), using initial pairs (v_0,v_2) and (v_1,v_3). This handles opposite eigenvalues of equal modulus as well: M² is then scalar, and both parity starts still must have the requested sign. A negative repeated eigenvalue with a Jordan block is also covered.

One must check the discriminant of M before this reduction. A pure-imaginary conjugate pair squares to a negative scalar, so “the square has positive roots” is not true without the real-spectrum hypothesis. The source performs the check in the correct order.

For a genuinely nonreal pair rho exp(±i theta), every nonzero real observation is rho^n times a nonzero sinusoid. If theta/(2pi) is rational, its values over one rotation period sum to zero. If irrational, its phases are dense. Either argument forces a negative term unless the observation vanishes identically. Therefore no strictly positive observation exists on such an orbit. A nonempty legal macro has at least one positive flight-time observation, making this entire spectral branch empty. This is stronger and simpler than attempting to decide each complex-spectrum guard by a generic recurrence algorithm.

### 3.3 Removing algebraic coefficients costs only degree two

For distinct roots of B, beta=(t−sqrt(Delta))/2. With A≥0, the sign condition B−beta A≥0 becomes

    C>=0 or (C<0 and Delta A²−C²>=0),  C=2B−tA.

The sign restriction before squaring is crucial. It prevents spurious solutions caused by squaring a negative quantity. The equivalence remains true at A=0. Repeated roots equal t/2 and are rational. Therefore all emitted tests are rational linear/quadratic polynomials in the initial gaps. Fixed positive denominator clearing yields integer coefficients without changing signs or degree.

This establishes the claimed effective quadratic-sign formula. It does not use, or imply, a general finite cutoff for recurrence positivity. An explicit exact-rational check in this audit has its first nonpositive term at index 6932, illustrating why short prefix checking is not a proof.

## 4. Unique-witness quartic: two independently checked routes

The initially proposed private-copy method is sound. Partition the input by complete sign patterns of finitely many integer quadratic polynomials F_j. For each permitted pattern choose a natural selector e_h with sum_h e_h=1 and private copies X_hi=e_h p_i. Replace F_j(X_h) by

    F_j(X_h)−F_j(0)(1−e_h).

This is zero when inactive and equals F_j(p) when active. For a strict signed atom append signed_lift−e_h−z=0; for equality use the lift itself. All residuals have degree at most two. Every inactive slack is forced to zero, and a complete sign pattern selects one branch. This avoids the invalid cubic residual e_h F_j(p). The checker's private-copy regression explicitly exercises a nonzero constant term and canonical inactive zeros.

The reviewed source uses a simpler direct construction. For each Q introduce e_−,e_0,e_+,z in N and impose the three Boolean equations, the one-hot sum, and

    Q−(e_+−e_−)(z+1)=0,  e_0 z=0.

For Q>0, the only natural solution is (0,0,1,Q−1); for Q<0 it is (1,0,0,−Q−1); for Q=0 it is (0,1,0,0). The final equation is essential: without it the zero branch would have arbitrary z and uniqueness would fail. The source includes it. Every residual is quadratic or lower, including when Q itself is quadratic.

AND, OR, and NOT gate outputs are then fixed by their quadratic/linear defining equations. Induction on a topological circuit order makes every output uniquely Boolean; extra Boolean equations on gate outputs are unnecessary. Requiring the final output to be 1 and taking the sum of squared residuals gives an integer polynomial of degree at most four. A natural zero exists exactly for accepted inputs and is unique. The stated ledger, 4A+J witnesses and 6A+J+1 residuals for A sign atoms and J gates, is correct before optional simplifications.

No generic MRDP theorem, unbounded history code, unknown exponential, square-root witness, or number-theoretic noncanonical decomposition appears. The compiler proves exactly the advertised single natural fiber per fixed encoded input. It does not select a unique numerator/denominator representation among multiple encodings of the same rational geometry. That distinction is a scope clarification, not a defect in the source's claim.

## 5. Observable clock and rational-limit audit

### 5.1 Summability depends on the observed sequence

The clock is u_n=ell M^n x>0, not the full matrix state. For either parity recurrence with roots alpha≥beta≥0:

- Both roots below 1 imply convergence, including a Jordan factor n
- alpha≥1>beta>0 permits convergence exactly when the alpha coefficient vanishes
- beta≥1 cannot support a summable strictly positive sequence
- With beta=0<alpha, strict positivity forces the nonzero tail coefficient, so convergence is exactly alpha<1
- For a repeated positive root, convergence is exactly that root<1

These are the source's cases. In the cancellation branch, A>0 and Delta>0 turn the algebraic equality into C<0 and Delta A²−C²=0. This uses only degree-two signs. Eigenvalue comparisons are between fixed algebraic constants and 1, so compiling them does not add variables or alter the polynomial degree.

The clock formula using both parities is also correct. Write t=tr(M²), h=det(M²), and a_e,b_e,a_o,b_o for numerator-input clock observations at powers 0,2,1,3. If 1−t+h≠0, the convergent sum is

    [b_e+b_o+(1−t)(a_e+a_o)]/[q(1−t+h)].

The denominator may be negative when a larger unstable mode is canceled; fixed sign normalization of numerator and denominator handles this. If that denominator is zero and a valid convergent clock exists, the eigenvalue-1 mode of M² is canceled and the surviving root is t−1<1. The sum is (a_e+a_o)/[q(2−t)]. A repeated root 1 cannot yield a strictly positive summable sequence. The source explicitly separates that case.

Comparison of T=L(p)/(Dq), D>0 fixed, with H/K, K>0, uses DqH−KL(p). This has degree at most two when p,q,H,K are variable integer inputs. Section time is fixed to zero in this degree claim. A fully variable rational initial-time offset with another variable denominator would require fresh degree accounting; the source does not silently include it.

### 5.2 The arbitrary-finite-population rational-limit theorem is valid

For any fixed finite rational matrix M and rational x, the clock generating function ell(I−zM)^(−1)x lies in Q(z). If the duration series converges, its value is the finite limit at z=1 of this rational function, by Abel's theorem. Cancellation of powers of z−1 shows that this limit is rational. This is a conditional rationality argument, not an assertion that arbitrary-dimensional positivity has been solved.

Number preservation lets one follow the kth **spatially ordered** position continuously through collisions: equal incoming positions are replaced by the same number of equal outgoing positions. Every such coordinate is uniformly Lipschitz with constant max|speed|. At a finite accumulation time, all ordered positions and all gaps therefore converge. The leftmost displacement per macro is another rational linear observation and is bounded in absolute value by max|speed| times the macro duration. Its absolutely convergent sum is rational by the same generating-function argument. A convergent gap observation has a rational limit by applying Abel's theorem to (1−z) times its rational generating function. Hence all ordered position limits are rational.

A named collision site in a fixed macro phase lies within one macro duration of an appropriate boundary position, with spatial difference bounded by max|speed| times that duration. These durations tend to zero in the Zeno case, so each such site's limit is one of the rational ordered-position limits. A finite rational prefix preserves the conclusion. Theorem C is therefore sound.

## 6. Independent derivation of the four-signal example

At section time zero use positions (0,0,d,d+y) with speeds (+1,+3,−1,−2), d,y>0. The +3 shuttle reaches the −1 right wall after d/4. It becomes a −3 shuttle and reaches the +1 left wall after another d/8. Thus the core cycle lasts 3d/8, the wall separation becomes d/4, and the spectator's distance to the right wall becomes y−3d/8.

Before the first bounce, the wall/spectator candidate is y, so the first bounce requires y>d/4. After that bounce, the remaining wall/spectator candidate is y−d/4, which must exceed d/8. The combined complete-cycle condition is exactly d>0 and y>3d/8. The right wall separates the spectator from the shuttle throughout any such cycle; there is no hidden spectator encounter. Equality y=3d/8 produces a simultaneous remote spectator/right-wall collision at the left bounce, which must be included in a complete batch and therefore invalidates the proposed two-bounce macro.

Induction on the algebraic return map gives

    d_n=d 4^(−n), y_n=y−(d/2)(1−4^(−n)),
    t_n=(d/2)(1−4^(−n)).

The first K complete strict cycles are legal iff y>(d/2)(1−4^(−K)). Taking the intersection over all finite K yields y≥d/2. The weak limiting boundary is correct. At equality the spectator reaches the limiting location only at time d/2, so every finite prescribed batch remains complete. No later dynamics is being asserted.

The return matrix has eigenvalues 1/4 and 1, but ell=(3/8,0) sees only the shrinking mode. All infinitely valid inputs are Zeno with total duration d/2. This is a real signal-machine counterexample to the proposed shortcut “Zeno iff spectral radius(M)<1,” not merely an abstract matrix counterexample.

For any K≥0 the integer seed d=4^(K+1), y=d/2−1 passes the first K cycles and fails the next. Thus no machine-and-word-dependent finite prefix horizon can decide infinite validity uniformly over all integer seeds. For positive integer inputs the infinite guard itself happens to have the canonical quadratic (2y−d−z)²=0; that easy example does not replace the general quartic proof.

## 7. Checks, limitations, and recommendation

The exact regression receipt is `check-results.json`. It records real-root/parity strict and weak cases, rational-radical sign elimination, both canonical arithmetic compilation methods, observable clock classification and sum formulas, and the displayed spectator return identities. Rejection of untested values is proved by the mathematical cases above, not inferred from finite enumeration.

I found no required correction in the reviewed source. In any report or summary preserve these boundaries prominently:

- A supplied fixed complete word, rather than arbitrary schedules or a universal nontermination frontend
- Strictly positive intervals and standard distinct-speed output groups
- Degree at most four with word-dependent arity; no constant-operation or optimal-arity claim
- Witness uniqueness per supplied input encoding, not a claim of canonical rational input representation
- Zeno classification from the observable clock with exact cancellation, not the whole spectral radius
- Validity of every finite pre-accumulation prefix; no post-accumulation execution semantics
- The all-population result is conditional rationality of limits, rather than effective recognition of validity in all dimensions

Primary-source cross-check: Becker et al., *Abstract Geometrical Computation 8: Small Machines, Accumulations and Rationality*, [arXiv:1307.6468](https://arxiv.org/abs/1307.6468), and the authors' [signal-machine introduction](https://www.univ-orleans.fr/lifo/Members/Jerome.Durand-Lose/Recherche/AGC/intro_AGC.html), support the standard rational signal-machine model and the distinction between speed bounds and general accumulation behavior. The more recent primary article [An Intrinsically Universal Family of Signal Machines](https://www.univ-orleans.fr/lifo/Members/Jerome.Durand-Lose/Recherche/Publications/2020_ToCT.pdf) states the distinct-speed collision convention. The specialized recurrence, compiler, and rational-limit arguments here were checked directly. No literature-priority claim or proof-assistant verification is made.
