# Mathematical verification review

## Conclusion

The amplitude convergence and all-orders Poincare expansion were checked by a separate technical review of the proof, together with fresh symbolic implementations. No material analytic defect or unresolved gap was found in the chain from the exact recurrence to a common positive amplitude and every finite algebraic order. This is a mathematical verification report, not publication, formal proof-assistant verification, or independent community peer review.

The rational coefficient field requires more than recursion over Q[a]: the cube-root rescaling also needs the mod-three grading argument. That argument was derived and checked separately and is included in Section 12 of the delivered article.

The proof genuinely uses the lower half of the Elvey Price–Fang–Wallner Theta theorem to establish strict positivity. It does not establish a rigorous numerical enclosure, an elementary value of the amplitude, or the analogous theorem for compacted trees. Its present qualifications accurately say so.

## Scope and reproducibility

Reviewed deliverable: `article/relaxed-binary-trees.tex`, SHA-256 4b24b3201e96fe662162cd189e325b1e5376a4a208d304f974da7fcbdf991af4. The integrated-source comparison and exact final PDF hash are recorded in `transcription-signoff.md`. References below to equations (F1)-(F36) use the delivered article's labels.

The prior paper was checked directly at https://arxiv.org/pdf/1908.11181. Theorem 1.1 gives precisely the relaxed-tree Theta estimate used here; the discussion immediately following it explicitly leaves existence of the amplitude open and gives 166.95208957 as an empirical estimate. Proposition 2.6 gives the starting recurrence. This audit does not assert that no later literature has resolved the problem.

The fresh programs in this directory do not import the main package's symbolic or numerical checkers:

- check_formal_independent.py and its JSON output reconstruct the nonautonomous polynomial recursion through degree epsilon^8, verify both boundary conditions and the grading at every computed order, and independently convert the logarithmic and endpoint coefficients
- check_frozen_and_spectrum.py and its JSON output verify the frozen residual exactly through epsilon^5, the exact gauge identities for every legal index with 1 <= N <= 40, the two original recurrences through N <= 40 and n <= 20, and the initial A082161 values; they also provide explicitly nonrigorous spectral diagnostics

Reproduction command, from the package root:

    python verification/run_checks.py

The immutable reference results are under `verification/expected/`; newly generated results are written under `output/verification/`. See `verification/README.md` for the individual commands and numerical qualifications.

The checks ran successfully with Python, SymPy 1.14.0, and SciPy 1.17.0. Finite symbolic and numerical checks supplement the arguments below; they are not substitutes for them.

## Exact recurrence and changing finite supports

The change from r to d and the factorial gauge are correct. At j = N the transformed recurrence gives d_(N,N) = d_(N-1,N-1)/N, consistently with r_(N,0) = 1. At j = 0 the omitted predecessor is exactly the prescribed zero boundary value.

The extra node N+1 in S_N is harmless and useful. Q_N(N+1) = 0, while a genuine preceding vector is supported at heights at most N-1, so S_N Q_N propagates it to heights at most N. The occupied parity restriction of psi_N also has maximal height N, since N+1 is the opposite parity. The preceding-parity singular vector h_N can have a component at N+1, but Q_N kills it; the stated small Q-defect controls it. There is no leakage into an unmodelled endpoint or silently constant-dimensional evolution.

All edge weights and all Q_N entries lie in [0,1]. Thus both the operator norm contraction and the entrywise comparison with the half-line adjacency operator hold on the padded space. The exact rational checks include j = N+1 in the first gauge identity and j = N in the second identity, not just bulk indices.

## Quadratic form, compactness, and min–max

The quadratic form (F6) is correct, including both special endpoints. Its first gradient edge has coefficient b_(N,1) = 1, so the explicit |v_0|^2 term produces diagonal coefficient two at the left endpoint without inventing b_(N,0). At the other endpoint the gradient contributes b_(N,N+1)|v_(N+1)|^2, and the displayed final potential restores diagonal coefficient two.

For 1 <= j <= N, the potential obeys

    2 - b_(N,j) - b_(N,j+1)
      >= (j-1)/(N+j) + j/(N+j+1).

After multiplication by N^(2/3), this bounds a fixed positive multiple of x_j, apart from an O(epsilon) constant. The last endpoint potential is at least one. The left endpoint can be absorbed into the same O(epsilon) allowance. Consequently the confinement estimate (F7) is uniform over the entire increasing support, including heights of order N.

Here is a precise interpretation of the interpolation used in the article. Add a zero node after the last finite node and extend the interpolant by zero thereafter. On each fixed x-window the edge coefficients are bounded away from zero and converge to one. The scaled discrete gradients therefore give local H^1 bounds. Their boundary contribution is exactly the interval between x = 0 and x = epsilon, enforcing zero trace. The confinement estimate bounds the sum of squared node values at x > R by C/R. The interpolated tail has the same bound up to an absolute factor and a single neighbouring interval.

On a fixed window, the difference between the interpolated L^2 norm and the nodal Riemann sum tends to zero by the local gradient bound. Tail control then extends this fact to the full half-line. Rellich compactness on each fixed window, followed by the uniform tails, gives strong L^2 compactness and retains normalization and orthogonality of finitely many eigenvectors. The limiting potential is 2x and the limiting gradient coefficient is one.

For min–max, compactly supported smooth zero-boundary functions give the recovery subspaces. Conversely, normalized low discrete eigenvectors have bounded scaled energies, so simultaneous compactness preserves their orthogonality, and the liminf bound applies to each vector in their span. This proves convergence of every fixed low eigenvalue and not just the ground-state Rayleigh quotient. The zero padding outside the finite matrix causes no competing low eigenvalues: it has scaled energy 2 epsilon^(-2), which diverges.

No quantitative compactness rate is needed in this step. The later finite quasimode supplies the quantitative estimates used by the evolution argument.

## Airy quasimode and weighted residual

The independent calculation expands the two square-root edge coefficients and the stated profiles, reducing derivatives with F'' = 2(x+a)F. Both F and F' coefficients vanish at every degree from epsilon^0 through epsilon^5. The sampled left boundary vanishes exactly.

The cutoff j <= 2 N^(1/2) gives x = O(epsilon^(-1/2)), hence x epsilon^2 = O(epsilon^(3/2)). Taylor expansions of the rational and square-root coefficients have uniform denominators there. Every fixed-order remainder is epsilon^6 times a fixed polynomial in x multiplying an Airy-decay envelope. Spatial Taylor displacements are O(epsilon). Such small displacements preserve an envelope of the form C(1+x)^d exp(-c x^(3/2)). The squared envelope has a uniformly O(epsilon^(-1)) sampling sum, while the unnormalized profile has norm asymptotic to epsilon^(-1/2) sqrt(I). This justifies the normalized O(epsilon^6) residual without losing an epsilon power.

The cutoff transition is at x of order N^(1/6), where Airy decay is exp(-c N^(1/4)). Any fixed polynomial loss from cutoff derivatives or finite shifts is negligible to all algebraic orders.

The coarse Airy gap locates the only eigenvalue within O(epsilon^6) of the candidate as the top one. Every other eigenvalue is at distance at least c epsilon^2; negative eigenvalues are much farther away. Spectral projection therefore gives the O(epsilon^4) normalized eigenvector approximation. Its sign can be chosen consistently with the positive Airy profile.

The three consequences in (F12) follow with the asserted strengths:

- The explicitly normalized samples change by O(N^(-1)) in l2 under continuous N variation; the two O(N^(-4/3)) approximation errors are smaller
- The sampled fourth moment bounds the l2 norm of j(j-1) times the profile by O(N^(2/3)); division by N^2 gives O(N^(-4/3)), and the eigenvector approximation has the same order
- The endpoint sample is F'(0) epsilon^(3/2)/sqrt(I); F'(0)/sqrt(I) = sqrt(2), and the absolute O(epsilon^4) eigenvector error is smaller than the leading endpoint by epsilon^(5/2)

The numerical diagnostics are compatible with these bounds. They are not used to infer their validity.

## Parity singular gap and scalar amplitude convergence

For a bipartite symmetric matrix S = [[0,B],[B*,0]], its nonzero positive eigenvalues are the singular values of B. The positive normalized eigenvector has squared mass 1/2 on each parity. Removing the top output singular direction leaves norm at most lambda_2 on all inputs, whether or not the input is orthogonal to the top input singular direction. This establishes (F14) in the exact form used in the proof. Treating minus lambda_N as an extra slow direction within a fixed occupied parity would be wrong; the article avoids that error.

The estimate involving Q_N g_(N-1) does require the explicit sample approximation at N-1. A crude multiplication of the O(N^(-1)) inter-time vector difference by I-Q_N would not give O(N^(-4/3)). The article explicitly makes the stronger argument, and the sampled moment bound supplies it.

The scalar equation (F17) is exact, since S_N g_N/lambda_N = h_N. The overlap defect of two unit vectors is quadratic, O(N^(-2)), while the Q-defect is O(N^(-4/3)). Thus t_N - 1 has the claimed summable order, although the vector k_N itself is only O(N^(-1)). The transverse recurrence gives ||w_N|| = O(N^(-1/3)), making the product <k_N,w_(N-1)> summable too. Boundedness of A_N comes from the contraction of the complete normalized evolution; it is not an additional hypothesis.

The convolution estimate (F16) holds for each fixed real power required here. Early times have exponentially small influence; within the last half of the interval, the effective memory length is O(N^(2/3)). The resulting O(N^(-4/3)) scalar increments prove a finite limit and its O(N^(-1/3)) convergence rate.

## Product normalization and strict positivity

The finite quasimode gives log(lambda_N) = log 2 + a N^(-2/3) + 3/(2N) + O(N^(-4/3)). The remainder is summable, proving the existence of a finite positive kappa. Formula (F23) has the correct zeta(2/3) and Euler-constant terms; it is an ordinary convergent real series, not a formal regularization.

Convergence of the scalar projection alone permits A_infinity = 0. The proof does not overlook this: the endpoint estimate would then imply an upper order smaller by N^(-1/3) than the established relaxed-tree lower bound. Theorem 1.1 of the cited paper excludes that possibility. This use of the prior theorem is explicit and noncircular.

The conversion N = 2n gives the correct normalization gamma = 4 kappa A_infinity. No fitted decimal value is substituted for this definition, and the article correctly declines a certified numerical enclosure.

## Endpoint smoothing

Entrywise domination of each positive changing-support kernel by J can be iterated after zero padding. Taking an l2 row norm preserves that comparison because the row entries are nonnegative. The squared row norm of J^ell is exactly the Catalan number C_ell, so its order is 4^ell (ell+1)^(-3/2). The denominator contributes 2^ell times a uniformly bounded factor on a block of length at most N^(2/3). This proves (F20) without a continuum heat-kernel assumption or an unproved endpoint eigenfunction expansion.

For the initial amplitude estimate, smoothing the O(N^(-1/3)) transverse norm over a block of length N^(2/3) gives O(N^(-5/6)). The inhomogeneous O(N^(-1)) forcing sums against (ell+1)^(-3/4) to the same order. Its ratio to the ground endpoint N^(-1/2) is O(N^(-1/3)), exactly what is needed for (F24).

For the later all-orders argument, Duhamel is applied directly to e_N, not to a changing projection error; this avoids introducing a new O(N^(-1)) forcing independent of the chosen approximation order.

## Arbitrary-order polynomial recursion

The operator identity in (F27)-(F28) is correct. Eliminating P produces an operator on Q that preserves polynomial degree with diagonal 4j+2; its off-diagonal terms only reduce degree in x. It is therefore invertible over Q[a]. A new scalar 2s_m in the forcing changes Q by the constant s_m. The boundary value G(0) = 0 is consequently exactly one nonsingular scalar condition, Q(0) = 0. The remaining integration constant in P is uniquely fixed by P(0)+Q'(0) = 0. This is an all-orders construction, not merely evidence from the first few profiles.

The time dilation is accounted for in both the spatial argument and epsilon_(N-1)^k. A new profile first enters through epsilon^2 times the Airy operator. The new h_k in log H first enters the ratio at degree k+3 with coefficient -k/3. Hence every prescribed finite ratio jet is realized by a genuine smooth positive H_N with its leading multiplicative constant fixed to one.

The independent replay reproduces s_2 through s_6 as printed and further finds

    s_7 = 221 a^2 / 3645
    s_8 = 7162009 a^4 / 413343000 + 3830611 a / 2296350.

These extra coefficients are checks of the recursive mechanism, not necessary additions to the theorem. Every computed profile satisfies the two normalization conditions exactly.

## Normalized all-orders residual

On the chosen cutoff support, -log D_N(j) <= C j^2/N, so multiplication by D_N^(-1) is uniformly bounded. At fixed scaled height D_N^(-1) tends to one, with the stated O(N^(-1/3)(1+x)^2) estimate. A cutoff substantially farther out would require a new gauge argument; the actual cutoff is safe.

The normalized residual is exactly the gauge transform of the original recurrence residual:

    z_N - M_N z_(N-1)
      = D_N^(-1) [Z_N - T_N Z_(N-1)] / P_N,

where T_N is the original recurrence map. The formal pointwise error has factor H_N, and H_N/P_N is asymptotic to kappa^(-1) N^(-1/6). The sampled polynomial-Airy envelope has l2 norm O(N^(1/6)), including parity restriction, so these factors cancel. Thus an O(N^(-p)) local envelope yields the same O(N^(-p)) normalized l2 error; no unrecorded norm loss is present.

The changing cutoffs add only superalgebraically small errors. The extension by zero does not create a large remote boundary residual because both the profile and every finite shifted value there already have the stated Airy decay.

The overlap limit is q_0 = kappa^(-1) sqrt(I/2). The factor 1/2 is the parity sampling density, and the factor sqrt(2) is the parity eigenvector normalization. This agrees with both direct summation and the claimed final amplitude.

## Zero-limit bootstrap and common amplitude

The second line of (F33) is an estimate of increments, not a forward contraction of the scalar. Its use is valid only because alpha_N tends to zero. That limit is already known from A_N tending to A_infinity and the proved overlap limit q_0, with C = A_infinity/q_0. No condition at infinity is imposed on the unknown counting solution.

If alpha_N = O(N^(-q)), the first line gives

    ||W_N|| = O(N^(-q-1/3) + N^(2/3-p)).

Substitution into the scalar increment produces summable terms of orders N^(-q-4/3), N^(-p-1/3), and N^(-p). Summing from N+1 to infinity therefore gives

    alpha_N = O(N^(-q-1/3) + N^(1-p)).

Starting from boundedness, finitely many iterations reach q = p-1 for every fixed p > 1. There is no logarithmic endpoint loss, since all summed exponents are strictly greater than one. The claimed ||e_N|| = O(N^(1-p)) follows.

Final-block smoothing improves the coordinate error to O(N^(1/2-p)); division by the leading normalized endpoint N^(-1/2) gives relative error O(N^(1-p)). Choosing p >= 1+(M+1)/3 and enough formal orders proves the theorem's remainder at each prescribed M.

Every truncation has the same H_N leading constant, the same limiting overlap q_0, and hence the same multiplier C. Finally 2 C F'(0) = 4 kappa A_infinity. The theorem does not conceal a different amplitude for each finite expansion.

## Coefficient field and numerical coefficients

The coefficient-field section's normalized formal Airy function phi_a has phi_a(0) = 0 and phi_a'(0) = 1. For omega^3 = 1, its scaling identity phi_(omega a)(omega x) = omega phi_a(x) follows by the ODE and both initial conditions. The transformed formal profile has the same leading term and normalized boundary data. Uniqueness of the polynomial recursion then gives s_m(omega a) = omega^(-m)s_m(a), and the triangular ratio-matching equation gives h_k(omega a) = omega^(-k)h_k(a).

The normalized endpoint Phi(a,epsilon,epsilon)/epsilon is invariant under simultaneous multiplication of a and epsilon by omega. Thus every relative or logarithmic endpoint coefficient b_k contains only powers a^r with r+k divisible by three. The substitution a = 2^(-1/3)z and N = 2n introduces 2^(-(r+k)/3), which is rational. This completes the missing field justification without altering the analytic proof.

The independent exact extraction confirms all three logarithmic coefficients and all three c_k in the main statement. It also checks the profile grading at every computed order through epsilon^8. The published fit and the local three-correction estimate remain numerical estimates with no certified error bar, as the article says.

## Presentation details resolved in the delivered article

The final article includes the coefficient-field argument, explicitly adds a final zero interpolation node, restricts the quadratic-form identity to the finite support, and states the choice p >= 1+(M+1)/3 for the requested remainder. It retains the distinction between an analytic existence formula, an empirical amplitude fit, and a certified numerical enclosure.

There are no unresolved substantive findings from this verification review.
