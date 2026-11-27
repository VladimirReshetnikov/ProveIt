# Source audit of lsernau/grh-lean

Date: 2026-11-27. Repository: <https://github.com/lsernau/grh-lean>.
Pinned commit: `72fead102f663d5c7a407964a13dc0cf9d977207` (the initial and current public commit, authored 2026-11-25).
Local read-only clone: `research/grh-lean/`. Per-file hashes and exact source URLs for the files inspected closely are in `audit_manifest.json`.

## Scope and conclusions

The endpoint is genuinely Mathlib's `RiemannHypothesis`, together with four ordinary statements about Mathlib's zeta and Dirichlet L-functions. It is not merely a theorem conditional on an unproved GRH-like analytic hypothesis. The endpoint statements are defined in `grh/src/Statements.lean`, which imports only Mathlib. In `grh/src/Main.lean`, all five theorems have closed types and are obtained from `New.grh`; `New.grh` itself has no mathematical assumptions beyond the definitions in that closed proposition. This source inspection provides no reason to reject the user's premise.

This review inspected the endpoint and the arithmetic/analytic reduction closely, and scanned the entire two source trees for common trust escapes. It did not read every proof of all background results and did not rerun Lean or the independent checkers. Neither `lean` nor `lake` was initially installed on the executable path in this workspace. A lexical scan is not a kernel check.

The source trees contain 803 Lean files / 477,124 lines (readable) and 794 Lean files / 112,827 lines (compact). A scan of both `src` trees for `sorry`, declarations of `axiom`, `native_decide`, `unsafe`, `opaque`, `implemented_by`, `extern`, `initialize`, `#eval`, and custom `elab`, `macro`, `syntax` returned only four innocuous occurrences of the English word "axiom" inside comments. `Challenge.lean` lives outside `src`, deliberately states the target with `sorry`, and is not an import of the solution. The source's claimed axiom footprint is `propext`, `Classical.choice`, `Quot.sound`.

## Independent verification evidence

Andrew V. Sutherland's MIT primary-source page <https://math.mit.edu/~drew/shortgrh/> is dated 2026-11-27 17:27 UTC and pins the same commit. It records both editions being built independently, compared to the challenge statements, replayed through Lean's kernel, and accepted by nanoda, lean4lean, con-leche, con-ron and paranoid Comparator. A run of the readable edition on a smaller machine was stopped for memory, explicitly without a rejection verdict; the larger-machine run accepted. The page also states that the proof has passed machine checks and has not received a complete human mathematical reading.

Three individual logs were opened:

- <https://math.mit.edu/~drew/shortgrh/readable-axioms.log>: each of the five theorems depends only on the three standard axioms, exit 0.
- <https://math.mit.edu/~drew/shortgrh/compact-axioms.log>: same, exit 0.
- <https://math.mit.edu/~drew/shortgrh/readable-standalone-con-ron-compare.log>: all five challenge theorems justified by the solution, 216,571 solution declarations accepted, exit 0.

These are published independent verification results, not checks run in this task. The MIT page additionally reports a new, separately checked Lean derivation of Schoenfeld's explicit psi bound from the compact RH proof. This is a verified consequence but is not novel mathematics and should not be presented as our new result.

## Exact exported mathematical scope

1. `riemannHypothesis : RiemannHypothesis`.
2. `riemannZeta_eq_zero_re`: if zeta(s)=0, s is not one of -2,-4,... and s != 1, then Re(s)=1/2.
3. `LFunction_ne_zero_of_half_lt_re`: for every modulus N>=1 and every complex Dirichlet character chi modulo N, primitive or imprimitive, Re(s)>1/2 implies L(s,chi)!=0, with the principal-character pole at s=1 excluded.
4. `LFunction_eq_zero_re`: every zero in 0<Re(s)<1 lies on Re(s)=1/2, for all Dirichlet characters.
5. `LFunction_eq_zero_re_of_isPrimitive`: the primitive-character specialization.

"GRH" in this repository means Dirichlet GRH. No endpoint here establishes GRH for arbitrary automorphic or Artin L-functions, the Ramanujan conjecture, zero simplicity, or linear independence of zero ordinates. New results using those would need separate hypotheses/proofs.

## Mechanism traced through the source

Let d be a prime congruent to 7 modulo 8, q a fixed modulus coprime to d, and chi_d(n)=(n/d). Define

    R_(q,d)(x) = sum_(n<=x, n=1 mod q) Lambda(n)(1-chi_d(n))(1/n-1/x)
                 - log(x)/phi(q) - c_(q,d),

where c is fixed by the logarithmic derivatives at 1 and also characterized by R(x)->0.

The geometric/arithmetic heart is a comparison of one covolume plus twice an integral index. Short forms and enough independent forms provide an upper bound; integral forms being long provide a lower bound. Their common main amount cancels. In `grh/src/New/Reduction/MainInequality.lean`, the final result is

    m * totalRemainder <= f * a * (log b)^5.

The data have m of order sqrt(x), log b at most 2*x^epsilon, and a much larger cutoff x_1 where the ordinary fixed-modulus prime number theorem controls the remaining terms. `New.eventually_primeRemainder_le_rpow` then proves, for every epsilon>0 and each permitted d,

    R_(q,d)(x) <= x^(-1/2+epsilon) eventually.

Only an upper bound is needed. The bridge is not silently assumed: `New.isPolar_primeRemainder` explicitly computes the meromorphic Laplace transform of R(exp(v)). At a point s!=0,1 with Re(s)>0 its residue is

    [sum_chi ord_s(entireL_chi) - sum_chi ord_s(entireL_(chi*chi_d))]
      / [phi(q) s(1-s)].

`entireL_chi` is L(s,chi), with the principal pole removed by the factor s-1 and its analytic value at 1. The file `Lib/Analytic/QuadraticTwist.lean` supplies, without using GRH, a prime d in the allowed progression for which every twisted L-function has no zero in a fixed box Re(s)>=beta>1/2, |Im(s)|<=H. It derives this from a quadratic-twist zero-density estimate and Dirichlet's theorem.

For that d, residues at real x>beta are nonnegative (orders are nonnegative and x(1-x)>0 in the possible zero interval). `New.IsPolar.landau` then turns the one-sided remainder estimate into the vanishing of every residue to the right of beta, by Landau's theorem for a positive Laplace measure. Therefore the untwisted zero orders are zero. The argument includes the real-zero issue; it does not assume real zero nonexistence in advance.

The general modulus q is handled by induction to the modulus 18480*q and removal of finitely many Euler factors, followed by the functional equation to reflect zeros to the critical line.

## Reusable inputs and extension opportunities

1. **Twist-dependent product formula.** `HeightLe` permits a different auxiliary twist at each p-adic place while retaining a common archimedean multiplier. `TwistedLattice.covolume_add_index_nonneg` then gives a global determinant bound. This is more reusable than treating GRH as a black box, but applying it in a genuinely new automorphic setting would require new integrality, spanning and congruence inputs.

2. **Sparse-family one-sided detection.** `zero_density_quadTwist` says that for beta=1/2+9*delta, at most O(X^(1-delta/2)) allowed d<=X have a twisted zero in a fixed box. Thus the one-sided criterion still works if the required remainder bound is known only for a set S of allowed primes with counting function not O(X^(1-(beta-1/2)/18)). Proof: S contains a twist with no zero in the box, then repeat `Criterion.lean`. Consequently a base zero rho with Re(rho)>beta forces failure of the eventual one-sided bound for all but O(X^(1-(beta-1/2)/18)) allowed d<=X. This is a clean extension of the formal criterion, but probably too short by itself to warrant the requested claim of a significant new theorem. Global originality would still need a literature search.

3. **Analytic transfer limits.** The actual analytic endpoint requires the residue sign, a zero-avoiding twist family, and the geometric size/divisibility inequality. A merely formal resemblance between Euler products is not enough to transfer the proof to Artin/automorphic GRH. A new theorem can be independent of the truth of those extensions if it states and proves a general operator, determinant, or positivity mechanism with all hypotheses explicit.

## Exact source links for the principal reductions

- <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Statements.lean>
- <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Main.lean>
- <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/MainInequality.lean>
- <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/OneSidedBound.lean>
- <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Zeros/Criterion.lean>
- <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Reduction/Zeros/PrimeError.lean>
- <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Lib/Analytic/Landau.lean>
- <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Lib/Analytic/QuadraticTwist.lean>

The audit conclusion is bounded: closed standard statements plus strong published independent machine verification support using Dirichlet GRH here; the present task is not itself a fresh complete formal verification of the 477,124-line development.
