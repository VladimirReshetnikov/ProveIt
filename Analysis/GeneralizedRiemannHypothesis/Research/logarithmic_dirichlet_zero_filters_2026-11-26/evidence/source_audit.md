# Source audit: RH and Dirichlet GRH

Audit date: 26 November 2026 (America/Los_Angeles). This is a source inspection and an examination of published verification records, not a local Lean rebuild. No remote repository was changed.

## Conclusion

The user's premise is supported by the current primary sources: RH and GRH for **Dirichlet L-functions** have formal proofs, and the particular shorter proof repository requested here has independent end-to-end verification records. A useful research report should accept those results in their precise scope, while distinguishing the supplied new argument from the verified upstream Lean artifact. The repository does not establish the corresponding statement for arbitrary nonabelian Artin or automorphic L-functions.

## Immutable snapshot

- Repository: <https://github.com/lsernau/grh-lean>
- Commit: `72fead102f663d5c7a407964a13dc0cf9d977207`.
- Git tree: `5eb1240f03e791edd3fc7aa84a3a7d8dc3997b7f`.
- Commit timestamp: `2026-11-25T20:38:07Z`; commit subject: `Lean proof of GRH`.
- Lean toolchain: `leanprover/lean4:v4.35.0`.
- Mathlib commit: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- Root tree fetched recursively: 1,950 entries, not truncated.
- The selected 14 source/document files in `source_snapshot/provenance.json` were fetched with the GitHub connector at this commit, saved locally, and compared with their Git blob SHA-1 identifiers. All 14 matched exactly. The upstream license, notice, and attribution file were also retained.

Canonical immutable base for paths below:
<https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207>.

## Exact theorem boundary

`grh/src/Statements.lean` imports only Mathlib and defines these propositions independently of the development's special instances and automation settings:

1. `RiemannZetaZerosOnLine`: every complex zero of `riemannZeta`, excluding the negative even integers and the conventionally assigned value at its pole 1, has real part 1/2.
2. `DirichletLNonvanishingRightOfHalf`: for every nonzero natural modulus N, every Mathlib complex Dirichlet character chi modulo N, and every complex s with Re(s)>1/2, L(s,chi) is nonzero provided chi is nonprincipal or s differs from 1.
3. `DirichletLZerosOnLine`: for every such modulus and character, any zero in 0<Re(s)<1 has real part 1/2.
4. `PrimitiveDirichletLZerosOnLine`: the preceding statement specialized to primitive characters.

`grh/src/Main.lean` proves five public theorems: `riemannHypothesis : RiemannHypothesis`, `riemannZeta_eq_zero_re`, `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, and `LFunction_eq_zero_re_of_isPrimitive`. The first is Mathlib's own proposition. All moduli N>=1 and imprimitive characters are covered. The Dirichlet statements do not concern zeros with real part <=0. The source does not assume simple zeros, rational independence of ordinates, pair correlation, or any general nonabelian GRH.

## Verification evidence and its limits

The repository's readable-edition README reports compilation, an axiom audit, independent export checking by nanoda, con-leche, and con-ron, and Comparator statement/proof checking. The compact README reports its corresponding checks. These are corroborated by a primary independent verification page and linked raw logs:

- Andrew Sutherland, *Verification files for the shorter Lean proof of RH and of GRH for Dirichlet L-functions*: <https://math.mit.edu/~drew/shortgrh/>. Page last updated 2026-11-26 20:46 UTC. It explicitly identifies commit 72fead10.
- Readable-edition axiom output: <https://math.mit.edu/~drew/shortgrh/readable-axioms.log>.
- Compact-edition axiom output: <https://math.mit.edu/~drew/shortgrh/compact-axioms.log>.
- Readable-edition full paranoid Comparator log: <https://math.mit.edu/~drew/shortgrh/readable-lake-comparator-paranoid-remote.log>.
- Compact-edition full paranoid Comparator log: <https://math.mit.edu/~drew/shortgrh/compact-lake-comparator-paranoid-remote.log>.

Both raw axiom logs list only `propext`, `Classical.choice`, and `Quot.sound` for all five theorems and finish with exit status 0. Both full Comparator logs finish successfully with exit status 0 after all listed kernels accept. The primary page explains that these runs build in a sandbox, compare the five statements, inspect axioms, and run Lean's default and paranoid kernels plus nanoda, lean4lean, con-leche, and con-ron. It also distinguishes an incomplete secondary readable-edition run stopped for memory: that is not a mathematical rejection. The compact edition passed independently on two machines.

The primary official endorsement of the original proof is the Lean FRO/Mathlib Initiative joint statement of 21 November 2026: <https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>. It endorses both the statement and proof after community checks. The community maintenance repository explicitly bases its main branch on this same shorter commit: <https://github.com/leanprover-community/riemann-hypothesis/blob/main/README.md>.

The original requested Wikipedia page now describes RH as a theorem and cites the joint endorsement and Alpoge's announcement: <https://en.wikipedia.org/wiki/Riemann_hypothesis>. It was read, but the primary pages above are stronger evidence for verification claims. Alpoge's announcement is <https://alpo.ge/remark.pdf>; it distinguishes the proved generalized result from an expected further extended result.

The GitHub API returned zero check runs and zero Actions runs for this commit. There is no hosted CI result to cite at that location; the substantive verification records are the external logs. Lean and Lake were not on the local command path in this audit, and the entire 300,000-line development was not rebuilt here. No source gap was identified in the inspected reduction. This audit does not claim a complete human review of every upstream argument.

## Mathematical mechanism inspected directly

The readable edition exposes a particularly usable analytic interface, even though its construction uses extensive arithmetic geometry.

### 1. Compare covolume estimates

`grh/src/New/Reduction/MainInequality.lean` combines three inputs: short integral forms, sufficiently many independent forms, and a lower bound on integral forms. One corrected logarithmic covolume is bounded above and below. The main term cancels, leaving

    m * totalRemainder <= f * a * (log b)^5.

This is `New.star_inequality`. The dimensional proportion is controlled below by 1/2. The integer m, the number of theta lifts, is chosen on the scale sqrt(x). The proof comments explicitly identify cancellation of period constants, divisibility gains, and size terms. A general comparison of determinant size and integrality is a possible source of transfer arguments, but the arithmetic inputs have to be rebuilt in any new setting.

### 2. A nonnegative smoothed prime sum

For a prime d, q>=1, and the quadratic character chi_d(n)=(n/d), define

    lambda_(d,q)(n) = Lambda(n) * (1-chi_d(n)) * 1_(n == 1 mod q),
    R_(d,q)(x) = sum_(n<=x) lambda_(d,q)(n)*(1/n-1/x)
                 - log(x)/phi(q) - c_(d,q).

The coefficients are nonnegative. The source uses `lambdaKResidueClass`, `lambdaKSum`, and `primeRemainder` in `grh/src/New/Reduction/Zeros/PrimeError.lean`. The constant is the real part at 1 of `logDerivMean`; it makes the remainder tend to zero for the relevant d and q.

`grh/src/New/Reduction/OneSidedBound.lean` obtains

    R_(d,q)(x) <= phi(q)*(log b)^6/m + |R_(d,q)(x1)|
                 + log(b)*|R_(d,1)(x1)|.

Here q is a multiple of 18480, d is congruent to q/2-1 modulo q, m lies between sqrt(x) and 2sqrt(x), and the secondary scale x1 is very large. Ordinary prime number theorem bounds make the two errors at x1 small. Appropriate scale choices give the eventual one-sided bound

    R_(d,q)(x) <= x^(-1/2+epsilon), for every epsilon>0.

The target statement is a one-sided upper bound; the proof does not assume a two-sided estimate in order to obtain GRH.

### 3. Convert Mellin poles to zero multiplicities

For E(v)=R_(d,q)(exp(v)), the transform

    integral_(0,infinity) E(v)*exp((1-s)*v) dv

is meromorphic in Re(s)>0 and has only simple poles away from the removable point at 1. At s it has residue

    [n_q(s)-n'_(d,q)(s)] / [phi(q)*s*(1-s)],

where n_q and n'_(d,q) are the sums of zero multiplicities of the relevant Dirichlet functions and their quadratic twists. This is `isPolar_primeRemainder`.

`grh/src/New/Reduction/Zeros/Criterion.lean` chooses a prime d in the required class for which the twists have no zeros in the finite rectangle under examination (`exists_entireL_quadTwist_ne_zero`, from a quadratic-twist density argument). The remaining residues on the real axis have nonnegative real part. A Landau positivity argument then forces every residue in the proposed zero-free region to vanish. Since the multiplicities are nonnegative integers, this excludes the putative zero. The freedom to choose d is essential: merely bounding a difference of logarithmic derivatives could otherwise hide shared zeros.

Finally, `New.grh` changes level to q0=18480q and removes the finite Euler factors. `New.zeros_on_line` and `New.zeta_zeros_on_line` use the functional equation to turn right-half-plane nonvanishing into the usual critical-line statements.

## Transfer principles and cautions for novelty

- The nonnegative coefficients, one-sided remainder control, and recovery of zero multiplicities from poles are the cleanest analytic interfaces for a new theorem.
- Positive kernels and smoothing can turn arithmetic information into transform or spectral information. Their smoothing order and zeros determine what information survives; any assertion of recovery must account for annihilated frequencies.
- Changing the collection of L-functions requires checking whether the new weights isolate the desired zeros without cancellation. Nonabelian Frobenius statistics are not automatically supplied by Dirichlet characters.
- Names beginning `New` and the division into `Lib` and `New` do not certify novelty. The guide explicitly says the naming is organizational and advises consulting literature sections. Several source steps (orthogonality, partial summation, the functional equation, Hadamard's bound, and Landau's principle) are established tools.
- The supplied new theorem should state exactly which of these verified upstream facts it uses. It should not be labeled Lean-formalized merely because its input theorem is formalized.

