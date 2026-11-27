# Source audit: RH/Dirichlet-GRH and reusable analytic interfaces

Audited on 26 November 2026. This is an inspection of selected source files and primary-source documentation, not an independent compilation of the complete development.

## 1. Exact revision and scope

Repository: <https://github.com/lsernau/grh-lean>.

Pinned revision: `72fead102f663d5c7a407964a13dc0cf9d977207`, committed 25 November 2026 at 20:38:07 UTC. Confirmed through the GitHub branch API. The readable edition is `grh/`; actual Lean modules are under `grh/src/`. Its toolchain is Lean `v4.35.0`; the Mathlib revision is `56a005855ea17e0b0958f73ec801ae140b0a1679`.

The four propositions in `grh/src/Statements.lean` import only Mathlib. `grh/src/Main.lean` exports five theorems:

| Lean theorem | Mathematical assertion |
|---|---|
| `riemannHypothesis` | Mathlib's `RiemannHypothesis` |
| `riemannZeta_eq_zero_re` | A zero of zeta other than the negative even integers (with the pole point 1 excluded) has real part 1/2 |
| `LFunction_ne_zero_of_half_lt_re` | For every modulus N >= 1 and every complex Dirichlet character, its L-function is nonzero in Re(s) > 1/2, with the principal-character pole at 1 excepted |
| `LFunction_eq_zero_re` | Every zero of every Dirichlet L-function in 0 < Re(s) < 1 lies on Re(s) = 1/2 |
| `LFunction_eq_zero_re_of_isPrimitive` | The preceding conclusion for primitive characters |

The GRH scope is Dirichlet characters, including imprimitive characters. It does not assert RH for arbitrary Artin, Hecke, or automorphic L-functions. The passage from the half-plane form to the critical-line form in `grh/src/New/Main.lean` uses the functional equation and reflection of zeros.

The repository README reports a full build and checks by independent kernels, with only `propext`, `Classical.choice`, and `Quot.sound`. Its axiom-inspection driver is `grh/scripts/PrintAxioms.lean`. No independent full build was performed here. The snapshots retain upstream copyright notices and Apache-2.0 license; `source_manifest.json` records their hashes and pinned URLs.

## 2. Present status of the user's premise

The current Wikipedia page describes the November 2026 proof and its formal verification. For a primary source, use the Lean FRO/Mathlib Initiative joint statement dated 21 November 2026: <https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>. It certifies both the mathematical statement and the formal proof, citing independent statement comparison and kernel checks.

Michael Rubinstein's own verification page, <https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/>, reports on 26 November that the compact edition's 794 modules and the full comparator checks passed. These are external verification reports, not checks reproduced during this task.

The appropriate stance is to accept the established RH and Dirichlet-GRH premise with this precise scope, while clearly identifying which new arguments have or have not been formalized.

## 3. Exact weighted remainder

Let d be an odd prime and q a positive integer coprime to d. Write chi_d(n) = (n/d), and let Lambda be the von Mangoldt function. Define

    lambda_{d,q}(n) = Lambda(n) (1 - chi_d(n)) 1_{n = 1 mod q} >= 0.

The repository remainder is

    R_{d,q}(x) = sum_{n <= x} lambda_{d,q}(n)(1/n - 1/x)
                 - (log x)/phi(q) - c_{d,q}.

Here c_{d,q} = Re G_{d,q}(1), and

    G_{d,q}(s) = (sum_{chi mod q} [(entireL(chi chi_d))'/entireL(chi chi_d)
                    - (entireL(chi))'/entireL(chi)] - 1)/phi(q).

`entireL(chi)` is L(s,chi) for a nonprincipal character and the entire continuation of (s-1)L(s,chi) for a principal character. The q=1 constant includes the contribution from this pole removal; it must not be replaced by an untwisted Mertens constant without recalculation.

Primary definitions: `New.lambdaKResidueClass`, `New.lambdaKSum`, `New.logDerivMean`, `New.primeRemainder` in `grh/src/New/Reduction/Zeros/PrimeError.lean`.

The same file proves `New.primeRemainder_eq_sum_posPart`. For u > 0 it immediately yields the useful convexity identity

    R_{d,q}(1/u) - log(u)/phi(q)
      = sum_n lambda_{d,q}(n)(1/n-u)_+ - c_{d,q}.

The right side is locally a finite sum of convex functions, hence convex. This is the precise repository input for a sampling or optimal-interpolation result.

## 4. The transform and the pole test

`grh/src/Lib/Analytic/EntireLFunction.lean` defines `New.IsPolar E r` by the following requirements: E is measurable; |E(v)| <= C exp(v) for v >= 0; its transform

    Phi(s) = integral_0^infinity E(v) exp((1-s)v) dv

for Re(s)>2 has a meromorphic continuation to the complex plane; all its poles in Re(s)>0 are at most simple, with residue r(rho). A zero of higher multiplicity is allowed: the logarithmic derivative still has a simple pole whose residue is that multiplicity.

`New.integral_primeRemainder` identifies the transform for E(v)=R_{d,q}(exp v):

    Phi(s) = [G_{d,q}(s)/s - G_{d,q}(1)]/(s-1).

For d = 7 mod 8, `New.isPolar_primeRemainder` gives the residue

    r(rho) = [n(rho)-n_twist(rho)]/[phi(q) rho (1-rho)],

where n is the sum of orders of the untwisted entire L-functions, and n_twist is the sum for their quadratic twists. The apparent singularity at 1 is removable.

`New.IsPolar.landau`, in `grh/src/Lib/Analytic/Landau.lean`, states:

* beta > 0;
* E(v) <= exp((beta-1)v) for all sufficiently large v;
* Re r(x) >= 0 for every real x > beta;
* E and r satisfy IsPolar.

Then r(rho)=0 at every rho with Re(rho)>beta. The proof constructs the nonnegative density K exp(beta v)-E(v)exp(v) and applies Landau's principle at its convergence abscissa. This is a known analytic principle; the repository itself credits Landau, Widder, and Montgomery-Vaughan.

## 5. Removing cancellation by auxiliary twists

The theorem `New.LFunction_ne_zero_of_primeRemainder_le` in `grh/src/New/Reduction/Zeros/Criterion.lean` has exact quantifiers:

* q0 > 0, with 8 dividing q0;
* d0 = 7 mod 8 and gcd(d0,q0)=1;
* beta > 1/2;
* for every prime d = d0 mod q0, R_{d,q0}(x) <= x^(beta-1) for all sufficiently large x (the threshold may depend on d).

Conclusion: for every character psi mod q0 and every rho != 1 with Re(rho)>beta, L(rho,psi) != 0.

The proof chooses one d for which every twisted entire L-function is nonzero in the box Re(s)>=beta, |Im(s)|<=|Im(rho)|. The helper is `New.exists_entireL_quadTwist_ne_zero` in `grh/src/Lib/Analytic/QuadraticTwist.lean`; it follows from `New.zero_density_quadTwist`. Consequently the unwanted n_twist vanishes in that box, and the target residue cannot cancel.

This means a new sampling criterion should first propagate sampled upper bounds to eventual upper bounds for each d separately, then invoke this existing theorem. No new arithmetic theta-lift input or full Lean rebuild is needed for the mathematical deduction.

## 6. Arithmetic proof architecture

`grh/src/New/Reduction/MainInequality.lean` combines three inputs: short integral forms with index control; sufficiently many independent forms, obtained through a second-moment/spanning argument; and a lower bound for integral forms obtained from twisted determinants and the product formula. The same covolume corrected by its index is estimated from above and below. Its main term cancels, leaving

    m * totalRemainder <= f * a * (log b)^5.

`New.eventually_primeRemainder_le_rpow`, in `grh/src/New/Reduction/OneSidedBound.lean`, then proves R_{d,q0}(x) <= x^(-1/2+epsilon) eventually for all epsilon>0 when 18480 divides q0 and d = q0/2-1 mod q0. The final `New.grh` applies the preceding analytic criterion after inducing the target character to level 18480q. Source inspection verifies these interfaces, not every transitive proof in the approximately 300,000 lines of the readable edition.

## 7. Prior-art boundary for sparse sampling

A directly relevant antecedent was found during this task:

Sandi Setiawan, *The Primacohedron Trace Formulation of the Riemann Hypothesis: A Guide to Reconstructing the Alpoge-Claude Proof in Lean*, v2, posted 25 November 2026, DOI <https://doi.org/10.20944/preprints202611.0738.v2>; author preprint at <https://www.preprints.org/manuscript/202611.0738>.

The full preprint was inspected. It proves an untwisted centered-trace chord bound with error (X-a)(b-X)/(2a), and a sufficiency theorem for sample gaps O(X^((1+theta)/2)). It explicitly obtains fourth-power sampling at the square-root scale and compares power grids. Thus neither the basic quadratic interpolation loss nor the fourth-power sufficient criterion should be advertised as new. Its later sections address the Mellin transform, signed dyadic averages, and an abstract lattice transfer.

The author-posted version at <https://www.academia.edu/181628231/The_Primacohedron_Trace_Formulation_of_the_Riemann_Hypothesis_A_Guide_to_Reconstructing_the_Alp%C3%B6ge_Claude_Proof_in_Lean> also contains a paragraph titled "Sharpness for convexity and endpoint data." It takes the convex trace to be the chord of the smooth main term and obtains a midpoint error at least (b-a)^2/(8b). Hence even single-interval sharpness of the quadratic loss is already present in the antecedent and must be credited. That paragraph explicitly allows the possibility that extra arithmetic information could improve the criterion. The publisher's version 2 PDF also contains this paragraph on page 4 of 8, Section 4, immediately after Table 1; its preceding results are numbered Proposition 2 and Theorems 1 and 2, whereas the author-posted rendering uses section-based numbering.

The strengthened construction developed in this task instead realizes all sample values as exact zeros simultaneously, using strictly positive uniformly bounded coefficients supported on all positive integers, and computes a nonremovable pole of its Mellin transform. No such global bounded-coefficient hidden-pole construction was found in the inspected antecedent. This is the precise distinction on which the candidate originality claim rests; it is not a claim of a complete literature search.

The exact logarithmic Jensen correction that arose during the investigation is log of the classical Specht ratio. It should also not be called new. For the standard formula, see Yuki Seo, Scientiae Mathematicae Japonicae 72 (2010), 165-169, <https://www.jstage.jst.go.jp/article/isms/72/2/72_165/_pdf/-char/ja>.

## 8. Primary references for the Li/probability direction

* Xian-Jin Li, *The positivity of a sequence of numbers and the Riemann hypothesis*, Journal of Number Theory 65 (1997), 325-333, DOI <https://doi.org/10.1006/jnth.1997.2137>.
* Enrico Bombieri and Jeffrey C. Lagarias, *Complements to Li's criterion for the Riemann hypothesis*, Journal of Number Theory 77 (1999), 274-287, DOI <https://doi.org/10.1006/jnth.1999.2392>; author PDF <https://websites.umich.edu/lagarias/doc/bombieri.pdf>.
* Masatoshi Suzuki, *Li coefficients as norms of functions in a model space*, Journal of Number Theory 252 (2023), 177-194, <https://arxiv.org/abs/2301.05779>. Its introduction fixes xi(s)=s(s-1)pi^(-s/2)Gamma(s/2)zeta(s)/2 and lambda_n=sum_rho[1-(1-1/rho)^n], with symmetric height cutoff and multiplicities. The Cayley map s -> 1-1/s sends the critical line to the unit circle.
* Masatoshi Suzuki, *Aspects of the screw function corresponding to the Riemann zeta-function*, Journal of the London Mathematical Society 108 (2023), 1448-1487, DOI <https://doi.org/10.1112/jlms.12785>.
* Takashi Nakamura and Masatoshi Suzuki, *On infinitely divisible distributions related to the Riemann hypothesis*, Statistics and Probability Letters 201 (2023), 109889, <https://arxiv.org/abs/2306.08317>. Its measure uses weights m_gamma/gamma^2 at the ordinates, has finite mass, and gives a compound Poisson law. This differs from the unweighted Cayley-angle jump measure accumulating at zero. The general RH-to-infinite-divisibility connection is therefore prior work, not a fresh claim.

Focused searches for Li-coefficient convolution semigroups, heat kernels, Cayley-angle Levy measures, small-time Cauchy limits, and all-order expansions found no primary paper giving the precise proposed Cayley-angle small-time expansion. This is a limited search, not proof of worldwide novelty. A nonauthor mathematical-knowledge site already refers to a Li/Schoenberg semigroup, reinforcing the need to place any novelty claim on the quantitative expansion rather than semigroup existence alone.

## 9. Other primary references highlighted by the user's overview

* Brad Rodgers and Terence Tao, *The de Bruijn-Newman constant is non-negative*, Forum of Mathematics, Pi 8 (2020), e6; corrected published-version preprint <https://arxiv.org/abs/1801.05914v5>. Together with RH this gives Lambda=0, a standard consequence rather than a new result.
* Luis Baez-Duarte, *A general strong Nyman-Beurling criterion for the Riemann hypothesis*, Publications de l'Institut Mathematique 78(92) (2005), 117-125, <https://arxiv.org/abs/math/0505453>.

