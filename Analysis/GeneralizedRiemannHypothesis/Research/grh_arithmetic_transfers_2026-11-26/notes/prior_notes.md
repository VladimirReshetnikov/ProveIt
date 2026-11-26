# Audit of the ProveIt GRH transfer corpus

Prepared 26 November 2026 for the parent analysis. This is a targeted audit of supplied research, not an independent verification of every manuscript in the corpus.

## Snapshot and artifacts

- Repository: `VladimirReshetnikov/ProveIt`.
- Pinned commit: `5cc267af75a635199ac5d93a7d49cbce521daefc`, committed 2026-11-26 19:57:48 UTC (11:57:48 PST).
- `docs/incoming` contains 46 ZIP research packages and one README. All 46 packages are GRH-transfer related. Their total downloaded bytes together with the README are 44,146,908.
- Latest incoming arrival: `1667e16cee9d4a68961e201e7288b8ecdac895c6`, 2026-11-26 19:24:40 UTC (11:24:40 PST). It added five archives: `grh_beyond_dirichlet_2026-11-25.zip`, `grh_method_transfers_graph_towers_and_finite_rings.zip`, `grh_transfer_bridges_2026-11-25.zip`, `grh_transfers_cycle_signings_and_lubin_tate.zip`, and `grh_transfers_density_gaps_and_zero_tests.zip`.
- All downloaded ZIP bytes match the exact Git blob SHA-1 identifiers returned by the GitHub connector. SHA-256 digests were computed independently. See `prior_archive_identity.json`.
- Complete 46-row audit ledger: `prior_audit_ledger.csv` and `prior_audit_ledger.json`. Every row gives archive, descriptive title, theme, main TeX member(s), exact source hashes, URL, reported proof status, and this session's review scope. Most rows are overview-level only.
- Local packages: `prior_archives/`; extracted content: `prior_extracted/<archive-stem>/`.
- The incoming README is 324,518 bytes but contains historical intake instructions for unrelated projects. It is not a GRH synthesis and should not be cited as one.

## Main assessment

The supplied corpus is much broader than the earlier personal-context summary. It is no longer accurate to characterize all the prior work as conditional nonabelian reductions. Several packages give complete paper proofs and substantial arithmetic certificates for concrete mathematical questions. This session directly checked the integer density-gap proof and its certificates; other completed claims remain described as reported until specifically audited.

The corpus also contains many equivalent prime-sum characterizations for nonabelian RH. None of the inspected summaries supplies the missing global arithmetic inequality for the conductor-23 cubic, discriminant-229 S3 frame, S4, A5, A6, PSL2, general Sylow, or symmetric-power targets. A new character detector by itself would mostly duplicate that work.

### Broad map of reported completed work

| Family | Concrete frontier in the supplied reports | Boundary |
| --- | --- | --- |
| Progression-free densities | Counterexample to the Asada et al. polynomial-density conjecture; improved natural-density constructions; McNew natural-vs-upper density gaps | Rankin's rational-ratio natural-density optimality and the comparison between integer- and rational-ratio natural extrema remain open in this corpus |
| Sparse singular moduli | Four-term and five-term classifications; `s<=5 iff h<=4`; exact maximal-support infinite families; Gaussian prime-conductor lower density above 99.981826% | A global six-term classification and density-one full support are not proved |
| Imaginary quadratic class groups | Reported completion of exponent-six census: 432 fields and 1236 orders; exponent-seven: 33 fields and 40 orders | These use published exhaustive finite censuses and, for the global cutoff, quadratic Dirichlet GRH; do not relabel them pure method-only transfers |
| Local torsion specialization | Sharp fixed-radius windows, exact shell costs, positive-tolerance regimes, finite coefficient fields, formal groups and Lubin--Tate interpolation | Global arithmetic applications still require actual modules, witness budgets, and compatibility |
| Graphs and finite rings | Full graph-tower example formulas; signed square-cycle optimum; reduced-ring positive-density criterion | General graph-tower algorithms, nonreduced finite-ring classification, and incompatible cycle lengths remain open |
| Arithmetic consequences | Heavenly varieties/isogenies, CM coefficient-field classifications, Mertens-error examples, prime representations | Many use only the exported Dirichlet theorem plus external known theorems; distinguish from internal-method reuse |

## Independently reviewed inherited theorem: McNew's density questions

### Exact provenance

Archive: `grh_transfers_density_gaps_and_zero_tests.zip`.
Main paper member: `grh_transfers/report.tex`.
Proof members: `grh_transfers/integers.tex` and `grh_transfers/integer_more.tex`.
Original checkers: `grh_transfers/checks/check_integer_gap.py` and `grh_transfers/checks/check_integer_prefix.py`.

These two proof members were read in full. Both checkers were read and rerun successfully. A new independent checker, `verify_density_gap_independent.py`, was written and run using a different primitive-ratio parametrization of geometric progressions, trial-division prime enumeration, and exact rational arithmetic. Its output is `density_gap_independent_result.json`.

The paper proves that the supremum of upper densities of sets avoiding three-term geometric progressions strictly exceeds the supremum among such sets having natural density. This holds separately for rational ratios and integer ratios. Write the four extrema as alpha, alpha_bar, beta, beta_bar with the usual conventions. The verified inherited claims are:

    alpha_bar - alpha > 0.002836,
    beta_bar - beta > 0.069218.

The second stronger numerical gap uses McNew's published `beta_bar>0.818410`. The simpler self-contained common certificate gives both gaps greater than 0.000404 and does not need that numerical lower bound.

### Proof audit

Fix Y>=12. Let S be the positive integers all of whose prime factors are <=Y, and write

    c = product_{p<=Y}(1-1/p),
    v = product_{p>Y}(1-1/p^2),
    B = c sup_A sum_{a in A}1/a,
    U = c integral_1^infinity J(t)dt/t^2,

where A ranges over admissible subsets of S and J(t) is the largest size of an admissible subset of S intersect [1,t]. Admissible means avoiding the chosen ratio convention.

1. For any global admissible set E with natural density d, split n uniquely as a rough part g times a smooth part h. Each fixed smooth fiber is admissible. Applying reciprocal weights and then partial summation gives `d<=B`. This uses one fixed fiber for all cutoffs and is the important distinction from pointwise finite optimization.

2. Restrict rough parts to squarefree integers. All three rough valuation vectors in a progression then coincide, since an arithmetic progression in {0,1} is constant. This makes independent fiber choices compatible globally. On successively very widely separated rough-part blocks, choose a fiber maximizing the count at the block's final cutoff. The resulting single admissible set has upper density at least `vU`.

3. Through 12 the greedy set is `{1,2,3,5,6,7,8,10,11}`, with nine elements, whereas `{1,2,5,6,7,8,9,10,11,12}` is admissible and has ten. No set can maximize every prefix, because a simultaneous maximizer would have to make every greedy decision. Hence every fixed admissible fiber loses at some prefix k<=12, and that unit loss persists on [k,k+1). Its weighted integral is at least `1/(12*13)=1/156`. Therefore `U-B>=c/156`.

4. Since U<=1 and `1-v<=sum_{p>Y}p^-2`, the density gap is at least

    c/156 - sum_{p>Y}1/p^2.

This is positive for sufficiently large Y; an exact interval certificate at Y=2000 with prime tail cutoff100000 proves it exceeds404/10^6. This completes both strict inequalities without any hypothesis about L-function zeros.

Every step above is mathematically sound on inspection. In particular, squarefree rough fibers prevent cross-block progressions, the reciprocal-weight natural-density bound does not assume density exists in each fiber, and the finite-prefix contradiction is uniform over the infinite smooth fibers.

### Exact rerun results

- Both ratio conventions have prefix maxima through12 equal to `[1,2,3,3,4,5,6,7,7,8,9,10]`; no admissible subset attains all at once.
- Independent exhaustive enumeration finds the exact least integrated prefix deficit `1/156` in both cases.
- Supplied common lower certificate: `404742119464902/10^18`.
- Independent common lower certificate floor at10^-18: `404742119469505/10^18`; its slightly larger value comes from a larger interval scale and exact rational product. Both prove only the claimed gap>0.000404.
- Rational ratio N80 prefix loss: `1553/45360`; Y293 certificate gives gap>2836/10^6.
- Integer ratio N80 prefix loss: `16567/132300`; Y83 certificate gives gap>13336/10^6.
- Four-prime integer-ratio weighted maximum through5000: `1619153731921/497871360000` across265 smooth integers.
- Consequently `beta <= 5245322990569/7001316000000 < 0.749192`.
- Combining with the cited lower bound gives `beta_bar-beta > 484624036991/7001316000000 > 0.069218`.

The 80-point and265-point certificates were replayed using the supplied algorithms after source inspection. The independent implementation checks the simpler12-point theorem and numerical positivity. Do not call the larger computations independent reimplementations.

### Primary literature check and its limits

The original author's current hosted manuscript, https://www.nathanmcnew.com/GPFsets.pdf, has Questions7.1 and7.3 on page15. It explicitly asks exactly the strict density comparisons above. It also distinguishes Rankin optimality (Conjecture7.2) and comparison between natural-density extrema (Question7.4), neither settled by the inherited proof.

Primary sources checked in the targeted current search:

- Nathan McNew, *On sets of integers which contain no three terms in geometric progression*, Math. Comp.84 (2015),2893--2910; author PDF above; arXiv1310.2277. Web refs: `turn618639233view0`, `turn164181396view0`.
- McNew's current research page, https://www.nathanmcnew.com/math.html, includes papers through2026. It lists the later progression articles below but no title announcing a natural-versus-upper gap theorem. This is a bounded observation, not proof of global priority. Web ref: `turn279122827view0`.
- *Counting primitive subsets and other statistics of the divisor graph of {1,...,n}*, European J. Combin.92 (2021),103237; https://arxiv.org/html/1808.04923v2. Theorem9 is an asymptotic for maximal finite integer-ratio GP-free subsets, not a theorem about one compatible infinite set of natural density. Web ref: `turn244489325view0`.
- Cao--Fang--McNew, *Note on sets without geometric progressions*, Integers22 (2022),A45; https://www.nathanmcnew.com/w45.pdf. It determines endpoints for greedy subsets of (0,1] and poses a different problem; it does not resolve these density comparisons. Web ref: `turn311476875view0`.
- Asada et al., *Avoiding 3-term geometric progressions in Hurwitz quaternions*, J. Integer Seq.27 (2024),24.7.7; https://cs.uwaterloo.ca/journals/JIS/VOL27/McNew/mcnew6a.pdf. Its main results concern quaternions; its opening comparison with Rankin is not a precise statement about the four distinct integer density extrema. Do not use that introductory sentence to infer a resolution of McNew7.1/7.3. Web ref: `turn504859773view2`.

Targeted searches found no later primary-source resolution of Questions7.1/7.3, but the search is not a comprehensive novelty audit. Safe phrasing: the supplied archive contains a proof of the precise questions posed in McNew's paper; this turn revalidated the argument and certificates. It was not newly discovered in this turn, and worldwide priority is not asserted.

## Nearest prior result for the new congruence-depth work

Archive `grh_structural_transfers_2026-11-25.zip`, members `grh_structural_transfers/sections/duality.tex` and `sections/symmetry.tex`, already establish:

1. A finite relation matrix imposes all intertwining equations over a DVR and modulo every power of its uniformizer. If its nonzero Smith valuations are a_j and rational kernel dimension h, the finite-level Hom length is `h*n+sum_j min(n,a_j)`.
2. The global source congruence term is finite iff the rational conjugate Tate-dual Hom space vanishes. A nonzero rational Hom forces linear divergence.
3. Anticyclotomic twists preserve the entire intertwining system and therefore cannot remove this obstruction.
4. The source mirror image is symmetric; an opposite-sign rational pairing permits a bounded smaller mirror target.
5. Under the source integral matrix-span condition and nonzero rational Hom, a primitive integral intertwiner is invertible and every finite-level Hom is the scalar line it generates. The symmetric length is n for the positive sign, or min(n,v_pi(2)) for the alternating sign.

The proposed refinement under residual absolute irreducibility with *zero rational Hom* is distinct from point5: the finite-level modules can be cyclic torsion of a fixed maximal congruence depth. No corpus match was found for Carayol, a trace discrepancy ideal, or that non-selfdual cyclic-depth statement. This is a scoped nonduplication result only. The broad Smith formula is already prior work, so the new presentation must say exactly what irreducibility sharpens.

## Remaining focused questions already identified by the latest corpus

- Can the actual CM points settle the tied local determinant at prime conductor42,337, the first conductor missed by the three Gaussian full-support tests?
- Can an arithmetic covolume comparison realize `2+tau(p)/p^(11/2)` or the conductor23 Artin trace? Optimizing a nonnegative polynomial is insufficient by itself.
- Can arbitrary rank-two graph-tower voltage data yield a terminating algorithm for both the eventual polynomial and its first valid level?
- Can products of nonreduced finite local rings be classified analogously to the reduced-ring density criterion?
- Can scalar/mirror congruence refinements be rebuilt in Lean under a genuinely admissible new arithmetic instance?

These are specific next steps. A generic new finite-group detector, an unqualified claim of K124 vanishing, or another unrestricted torsion shell theorem would either repeat prior work or exceed what has been proved.
