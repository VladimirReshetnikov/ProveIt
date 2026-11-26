# Source mechanism and transfer assessment

## Snapshot and formal scope

Inspected commit: `72fead102f663d5c7a407964a13dc0cf9d977207` of `lsernau/grh-lean`, dated 2026-11-25. All paths below are relative to that pinned repository. The statement layer is `grh/src/Statements.lean`; it imports only Mathlib and quantifies over `DirichletCharacter ℂ N`. The final endpoints therefore cover the Riemann zeta function and all Dirichlet characters over Q, not arbitrary Hecke, Dedekind, Artin, or automorphic L-functions. The auxiliary proof develops theories over CM fields, but that does not enlarge its endpoint.

The README reports Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, proof dependencies `propext`, `Classical.choice`, `Quot.sound`, and independent export checks. These are repository-reported checks. This analysis did not rerun the full build. The source explicitly reports that no mathematician has read the proof through. This need not obstruct examining the mathematics under the user's premise.

Permanent source base: <https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207>.

## The actual proof engine

The mechanistic spine is unusually concrete and transferable in parts.

1. **Prime sums become divisibility.** Jets of algebraic theta functions encode a weighted prime-power sum. At a prime p, local formal-group analysis supplies divisibility of those jets. Composite theta lifts, including corrective Hecke operators at exceptional primes, aggregate the divisibility gains. Source: `New/Derivatives/*`, `New/UpperBound/Divisibility/LocalDivisibility.lean`, `New/UpperBound/Size/ShortColumns.lean`.
2. **Divisibility is compared with archimedean size.** After dividing out a prescribed product of prime powers, integral source forms have controlled complex norms. This is Theorem A: `Data.span_short_integralRamified_eq_top` and `Data.indexLe_normalizedPoincare` in `New/Reduction/ShortAndEnough.lean`.
3. **Enough of the target is reached.** A second-moment argument for translated Poincare series produces many linearly independent target forms. Theorem B is `Data.enough_forms`; its proof descends from `New/Spanning/SecondMoment/SpanningTheorem.lean`. The independent family has n at least `(1-4/b^2)D`, where D is the target dimension.
4. **A determinant cannot be too small.** Theorem C, `Data.integral_forms_long` in `New/Determinant/Twist/LongForms.lean`, uses the product formula, regular families of anticyclotomic twists, and the height of ratios of theta-lift Gram determinants. The abstract package is `TwistedLattice.covolume_add_index_nonneg` in `New/Reduction/Lattices/TwistedLattice.lean`.
5. **The large main terms cancel.** `star_inequality` in `New/Reduction/MainInequality.lean` proves `m * totalRemainder <= f * a * logB^5`. Thus the argument is not merely an application of positivity or an explicit formula: it manufactures two opposite bounds for the same determinant and cancels the main term.
6. **The resulting one-sided prime bound detects zeros.** `New/Reduction/OneSidedBound.lean` gives, for every small epsilon and all large x,

   `R_q(x) <= (64 phi(q)+3) x^(-1/2+6 epsilon)`.

   Here `R_q(x) = sum_{n<=x,n=1 mod q} Lambda(n)(1-chi_d(n))(1/n-1/x) - log(x)/phi(q) - c_q`.

7. **Auxiliary twists remove cancellation.** In `New/Reduction/Zeros/Criterion.lean`, the Mellin/Laplace residue at rho is

   `(sum_chi ord_rho L(s,chi) - sum_chi ord_rho L(s,chi chi_d)) / (phi(q) rho(1-rho))`.

   A separate zero-density/twist-selection theorem chooses d so the second sum vanishes in a prescribed rectangle. Landau's theorem for a one-sided bound then kills the remaining nonnegative zero count. Exact theorem: `New.LFunction_ne_zero_of_primeRemainder_le`; analytic core: `New.IsPolar.landau` in `Lib/Analytic/Landau.lean`.

The mechanism has three coupled pieces: an arithmetic determinant construction, a non-cancellation device, and a zero-detecting transform. Porting only one does not establish the target RH.

## A reusable quantitative lemma extracted from the comparison

The following elementary proposition is an exact abstraction of the source's cancellation step, with the spanning fraction left variable. It is useful for screening extensions. It is not claimed as a historically new theorem.

**Proposition (partial spanning and error budget).** Let D,n,m,eta be positive real numbers with `eta D <= n <= D`. Let U,L,I be nonnegative, A+U nonnegative, and suppose real V,delta,R satisfy

`D(A-L) <= V+2 delta`, `V <= n(A-m R+U)`, `delta <= D I`.

Then

`R <= (U+L+2I)/(eta m)`.

**Proof.** Combining the inequalities gives

`n m R <= (n-D)(A+U) + D(U+L+2I) <= D(U+L+2I)`.

Divide by the positive n m. Because `n >= eta D` and the numerator is nonnegative, the displayed conclusion follows. All signs are needed; one must not replace a lower bound for n in an inequality with a potentially negative numerator.

For asymptotic parameters, if `m >= x^alpha`, `eta >= x^(-lambda)` and the normalized error budget is `x^(u+o(1))`, the output is `R(x) <= x^(-alpha+lambda+u+o(1))`. Therefore square-root strength requires `alpha-lambda-u >= 1/2`. In the source, the source images occupy a fixed positive fraction, m is of order sqrt(x), and the remaining logarithmic loss can be made `x^epsilon`.

This explains why a bounded amount of missing span is harmless, but a polynomially small spanning fraction is expensive. It also explains why formally increasing m is not a free improvement: the admissible-data definition constrains m to `[sqrt(x),2sqrt(x)]`, while local divisibility, gap sizes, and the Selmer budget depend on m.

## The strongest independent arithmetic theorem already inside the proof

`New.Selmer.exists_anticyclotomic_twist`, in `grh/src/New/Congruences/Selmer/GeneralTheorem.lean`, is a genuine independently useful endpoint. Its scope is broader than the final RH statements and its conclusion is not a routine consequence of RH.

The data are a CM number field E, a prime ell, a coefficient DVR O, a finite set S0 containing the ell-adic places, an inertial element g0 away from ell, finitely many compatible Selmer data T_i, and finitely many Stickelberger systems Y_k. A torsion-level and residue-field size condition (`IsTorsionLevel`) must hold. Given m >= 1 and epsilon > 0, it constructs a finite auxiliary set Q and an anticyclotomic character psi of ell-power order so that **all powers** psi,...,psi^m satisfy simultaneously:

- controlled Selmer normalized lengths `length(Sel_Q(T_i psi^j)) <= beta_i+epsilon`;
- controlled valuations of the values of the group-ring systems `v(psi^j(Theta_{k,Q})) <= beta_k+epsilon`;
- small total valuations `sum_{w in Q union conjugate(Q)} v(psi^j(gamma_w)-1) <= epsilon`;
- tame ramification exactly at the required auxiliary primes and triviality at decomposition groups above ell.

The `beta_i` are explicit global/local costs, including terms involving `det(rho(g0)-1)`, not arbitrary zero constants. The auxiliary primes, character order, and coefficient field can depend on epsilon and m.

The more specialized theorem `New.Selmer.exists_mFoldTwist_hasDivisibleSelmerLengthLe` in `TwistingTheorem.lean` applies this to the main summands of the constructed theta lifts. Its hypotheses include `IsMainSummandLike`, conjugate self-duality, control of Hodge jumps and inertia, and the specific admissible CM field. Its error is `(4f+3)r v_ell(chosenGroupOrder)+2^(-ell)`.

This is an excellent near-term target for extraction into a standalone arithmetic theorem and for comparison with horizontal p-adic nonvanishing methods. It does not, as stated, settle Goldfeld, BSD, the Bloch-Kato conjecture, or a specified fixed-order twist conjecture.

## A rigorous obstruction to a tempting Selmer inference

**Proposition (small normalized length does not force vanishing).** For each prime ell there are nonzero modules M_N over coefficient DVRs O_N with `length_norm(M_N) -> 0`, where normalization means `length_norm(O_N/ell)=1`.

**Proof.** Let `O_N = Z_ell[zeta_{ell^N}]` and `pi_N = zeta_{ell^N}-1`. The cyclotomic extension is totally ramified of degree `e_N = ell^(N-1)(ell-1)`, with pi_N a uniformizer and ell a unit times `pi_N^e_N`. Put `M_N = O_N/(pi_N)`. Its ordinary O_N-length is one and that of O_N/(ell) is e_N. Hence its normalized length is `1/e_N -> 0`, although `M_N` is nonzero for every N. For ell=2 start N>=2 to avoid irrelevant initial degeneracy. QED.

This is a logical limitation of the bound alone, not evidence that the actual constructed Selmer groups are nonzero. If a common coefficient field with ramification index at most e0 were available and a nonnegative length bound were <1/e0, vanishing would follow. Alternatively a fixed representation's Selmer corank is forced to vanish by finite total length, but proving that the source's local-condition module equals a conventional Selmer group still requires an explicit comparison. One must distinguish corank zero, finite nonzero torsion, and zero.

There is a second quantifier issue: `exists_isRegularFamily` in `New/Congruences/FitTwistsExist.lean` produces a twist **for each prime and p-adic embedding**. It does not produce a single global twist simultaneously good at all primes. The determinant argument is designed to permit that local choice. Any global arithmetic application requiring one character good at every ell needs a new theorem.

## Concrete extension targets and what is missing

| Target | Reusable part | New theorem needed | Assessment |
|---|---|---|---|
| Simultaneous nonvanishing / controlled divisibility in horizontal anticyclotomic families | General twisting theorem, torsion specialization, Stickelberger systems | Verify target family's norm relations and local conditions; obtain prescribed order or density if desired | Best immediate theorem-extraction opportunity; do literature comparison before novelty claim |
| Hecke RH over a fixed nonabelian number field | Twisted determinant formalism, theta/Selmer infrastructure, Landau criterion | New prime-ideal detector, replacement for the CM period cancellation, uniform source/spanning/determinant estimates, and auxiliary twists with no cancellation | Plausible research program; no completed extension follows from source |
| Automorphic RH for a specific GL(2) cusp form | Norm identities and congruence control | Detector for its signed Hecke coefficients or a positive Rankin-Selberg object preserving its individual zero information; correct gamma/period main term; twist zero avoidance | High-risk, very substantial new work |
| Artin holomorphy or nonabelian Artin RH | Some Galois and base-change tools | Analytic continuation/holomorphy and nonabelian constituent separation; Dirichlet character orthogonality alone cannot see those constituents | Not solved by replacing characters with representations in existing code |
| Fixed-order Goldfeld/DFK-style twist conjectures | Simultaneous twist selection idea | Prescribe fixed order, conductor counts, density, and central-value parity; existing output permits growing ell-power order and moving ramification | Source does not meet the conjectures' quantifiers |
| Simplicity or pair correlation of zeta zeros | Almost none beyond real-part exclusion | Control of multiplicities or correlations; a nonnegative total order detector only detects existence | No direct transfer established |

For arbitrary automorphic targets, sign-changing coefficients alone are not a proof that transfer is impossible: Rankin-Selberg constructions can restore some positivity. The real issue is whether this retains the individual target's zeros and permits exact determinant/period cancellation with sufficiently small losses.

## Literature and source pointers

- Repository reading guide: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/GUIDE.md>.
- Main comparison: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/MainInequality.lean>.
- General twisting theorem: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Congruences/Selmer/GeneralTheorem.lean>.
- Kriz and Nordentoft, *Horizontal p-adic L-functions*, arXiv:2310.20678v3, last revised 2025-11-16: <https://arxiv.org/abs/2310.20678>. Their abstract already states simultaneous nonvanishing for arbitrary finite collections of elliptic curves and applications to Diophantine stability. Thus "simultaneous nonvanishing" by itself is not a novelty claim.
- Mazur and Rubin, with appendix by Larsen, *Diophantine stability*, arXiv:1503.04642v3: <https://arxiv.org/abs/1503.04642>. Existing work already obtains infinitely many cyclic prime-power degree extensions preserving rational points under hypotheses.

## Validation limits

These findings are based on direct inspection of theorem declarations and proof summaries in the pinned source and the main cancellation proof, not a full independent check of 300,000 lines. The two propositions in this note have complete ordinary mathematical proofs. No Lean compile has been performed for this note. No major named open conjecture is claimed resolved.
