# Independent review: maximal parallelism and exact word order (808b53ed8)

The mathematical constructions and their stated limitations pass this review. I found two concrete input-contract defects in the maximal-parallel Python compiler and supplied a narrow, tested repair. No theorem-level defect was found in the order report. Neither report improves the 87-operation universal bound or instantiates a new universal Diophantine polynomial.

## Provenance and scope

Original archives, left unchanged:

- `/home/codex/.codex/worktrees/2a71/Proofs/docs/incoming/Maximal_Parallel_Diophantine.zip`, SHA-256 `e6a3dcfc419f2fb49552d5c4d0a17959f4360b9610799ef8190a27a2938a8066`.
- `/home/codex/.codex/worktrees/2a71/Proofs/docs/incoming/Order_Is_Not_a_Moment.zip`, SHA-256 `2cd366ff60ac48dfb6138a00871cc32ae4bd6f6778ddac2a590cd1559664aacc`.

The archives were safely extracted, rejecting duplicate paths, traversal, absolute paths and symbolic links. All member digests are recorded in `incoming_substrate_review_808b53ed8.json`. Below, P means the extracted `Maximal_Parallel_Diophantine` package and O means `order_is_not_a_moment`.

Read scope: the complete P `article.tex` (1,637 lines), compiler (460), verifier (241), README, proof and source audits; the complete O `article.tex` (979), compiler (387), verifier (263), and README. Every theorem and proof in both sources was read. Exported polynomials were rebuilt and checked. The PDFs were not visually reviewed or rebuilt, and no Lean formalization was run. This is a conventional mathematical and finite executable review, not a proof-assistant certificate or exhaustive literature novelty audit.

The portable checker `incoming_parallel_order_checks_808b.py` takes `--parallel-root`, `--order-root`, and `--receipt`. It pins both article/compiler/verifier triples before importing the supplied code, and runs original checkers in private temporary copies. Its deterministic result is recorded under `independent.parallel_order` in the batch receipt.

## Actionable findings and precise repair

**P2: Network retains mutable nested input containers.** P `code/parallel_certificates.py:109` validates but does not snapshot `consume`, `produce`, or `guards`. The frozen dataclass therefore does not own its accepted input. A valid minimal example is `consume=[[1]]`, `produce=[[0]]`, construct `Network`, compile `RoundCertificate`, and construct the witness for x=(1), f=(1). Change `consume[0][0]=2`. The compiled polynomial is still zero on that witness, while `network.legal((1,),(1,))` is now false and the exported metadata describes consumption 2. Both old and new matrices separately satisfy the mathematical matrix restrictions; the mismatch is stale compiled meaning versus live metadata/semantics.

**P2: Guard polarity is interpreted inconsistently without an exact Boolean check.** P `code/parallel_certificates.py:91` lacks Atom validation, and Network's guard check at line 124 omits polarity and the exact species type. `Atom(0,1,2)` is accepted. At x=(1), `holds` compares the threshold truth value with 2 and returns false, while the compiler at line 212 tests the truthiness of 2 and selects the positive branch. The valid True-guard witness with f=(1), y=(0) gives zero in the malformed-guard compiler although its own semantic `legal` method rejects the firing. Floating species indices and Boolean indices also pass the old range check; the former later fail at indexing.

These are implementation input-contract defects, not counterexamples under the mathematical hypotheses. The ordinary tuple/Atom inputs used by the author are unaffected.

`maximal_parallel_immutable_guards.patch` repairs just this boundary:

- Exact natural integer predicate (reject int subclasses as well as bool/float).
- Atom validates a natural species index, positive natural threshold, and exact bool polarity.
- Network takes nested immutable tuple snapshots of both matrices and guard conjunctions, rejects non-Atom guard values, then runs its existing dimension/support/species checks.

No residual, comparator, count, operational rule, or polynomial is changed. Public polynomial objects remain intentionally mutable; this patch does not claim to make every compiler object immutable or guard deliberate `object.__setattr__` bypasses.

Original compiler SHA-256: `27cb3689fa8329f940055489756a977befd98ee2ab4b2c59651451d440f26111`.
Patched compiler: `3562772c879ea092045d6963f13c35ccdcfd7f3e3605457dc6c3cb3a7c17d09b`.
Patch: `eeea36e7beefaa9a3ebd4ee5f6686c56ddfcc1ae464f8c8027d26d2fc83bbfd6`.

The portable `incoming_maximal_parallel_repair_checks_808b.py --original-root P --patch PATCH --receipt OUT` pins the original compiler/verifier and patch, copies the package to a private temporary directory, applies the patch, checks the exact patched digest, runs focused tests and the full author suite. The batch receipt under `independent.parallel_repair` records: 57 malformed rejections, 17 nested snapshot cases, 328 valid export equivalences, 1,600 canonical-assignment equivalences, a 500-digit state fixture, two exact CLI export comparisons, and successful patch dry-run. Both original data JSON files remain byte-identical after the author suite. These checks cover nested matrix/guard/outer-list mutation, generator containers, exact scalar types, invalid dimensions, and out-of-range species.

## Maximal-parallel mathematics

The one-copy extension argument correctly equates coordinatewise maximality with a deficient residual resource for every rule. Feasibility is `Af <= x`; same-round products cannot be reused. Equal rule columns retain distinct labels. Maximality is not maximum-cardinality firing. Every rule consumes something, giving finite branching and bounded extent height. Priority semantics, dynamic topology, and model-specific membrane rules are explicitly outside the automatic translation.

For fixed consumption/production coefficients, each threshold comparator has exactly one natural four-tuple. The two affine squares and two unsquared nonnegative products force complementary bits and kill the inactive slack. Shared threshold flags are consistent. The final maximality slack is uniquely determined once the extent is fixed. The certificate is nonnegative on the entire real nonnegative orthant, but is not generally convex.

Endpoint-supplied ordinary rounds use `d+2m+4H` witnesses, `2d+2H+m` affine squares and `2H` products. Extents are included in the witness count. A T-step certificate uses `T(2d+2m+4H)` witnesses. First halting adds a nonempty-extent slack at each earlier step and a direct terminal threshold bank: `T(2d+2m+4H+1)+4H+m`. T=0 and deadlock stuttering are handled correctly. This is a horizon-indexed family, not one fixed-arity unbounded-time equation. The implemented history class supports only ordinary, unguarded, retaining histories; guarded/flat one-round compilation does not silently imply those history interfaces exist.

The guard and flat formulas have correct truth tables: disabled rules cannot fire; an enabled unused flat rule must lack residual resources; used flat rules cannot be appended. Guards read x, not the residual or output. Retention modifies only the output balance. The direct register-machine embedding requires a single control token and the stated inhibitor test; its converse and exact halting time follow by induction. No numerical universal-machine table is instantiated here.

The resource-cover exponent proof is sound. A chosen cover's residual entries lie below the fixed maximal threshold; fixing nonpivot extent coordinates leaves at most one solution. For sharpness, integer kernel perturbations of `n*1` preserve zero residuals on a rank-minimizing cover and can be made feasible everywhere else. This gives the exponent for every consumption matrix. The fixed-T Presburger counting result and population-height bound then give degree at most `T(m-rho(A))`. Guarded systems need an enabled-submatrix analysis and are correctly excluded from that unguarded exponent claim.

The convex deadlock obstruction uses rational polyhedral zero sets and two nonnegative integral recession directions correctly. The degree-at-most-three semilinearity proof handles each exact support face and uses an interior natural zero to obtain rational affine equations. Its degree-four necessity conclusion is restricted to global real-orthant nonnegativity, not an unrestricted cubic impossibility. Program-uniform numerical stoichiometry still fixes dimensions/support and uses one comparator per support entry; it is not arbitrary-table or unbounded-time compression. The #P statement uses Turing reductions, while the specific private-leaf graph map is parsimonious; these are correctly distinguished.

## Order mathematics and computational scope

The gap equations recover multiplicities and moments exactly; within-gap binary pair counts fill the entire capacity interval. The converse constructs one common word. The ternary no-holes proof is sound: within-gap swaps change K_AB by one, paired opposite C-crossings preserve the A/B projection, and the sum of squared gap indices decreases until both letter populations reach their unique balanced gap vectors. Sorting within the gaps connects every word to one common normal form. The normal form is not assumed to be an extremizer.

For c=2, eliminating total/moment equalities gives the stated integer rectangle. Bilinear extrema occur at its corners. The crucial no-holes theorem then fills the interval between the independently attained lower and upper extrema. The 24-variable triangular sign/floor/slack system correctly forces unique witnesses, including ties, zero populations and rejected inputs with negative candidate slacks. The output has degree four and 297 expanded monomials. The smaller c=2 gap certificate has eight witnesses and six residuals; the 24-witness version improves uniqueness and direct evaluation, not witness count.

The four-letter congruence-hole family is correct: K_CD=3 forces CDCD, the B moments force the CB^bDCD skeleton, and equality of the two A-height sums confines A to equal-height gaps. This yields exactly `{b*j:0<=j<=floor(n/2)}` and the integral convex-hull counterexample. There is no claim that affine profile inequalities with integer restriction suffice.

The Heisenberg lift pays for both pair orientations and the same-letter binomial terms, doubling central equations to remove division. It adds 3r coordinate equations and no witnesses to a supplied profile. With c=2 but a target-only interface, five profile parameters become existential, giving 13 gap or 29 canonical witnesses; uniqueness need not survive this projection. The finite direct-power universality citation does not establish universality of these three-generator/supplied-multiplicity slices.

The supplied-c decision theorem is valid. A nonzero g/h determinant in any factor fixes the two remaining multiplicities by horizontal coordinates, reducing to finite profile search. If all such determinants vanish, g and h commute; the doubled logarithmic collection identity is linear in a,b,p,q because c is supplied. Moment-fibre nonemptiness suffices when K_AB has zero coefficient. The finite carry-automaton argument decides the resulting natural linear system. Allowing an existentially unbounded c is correctly not included.

## Bounded arithmetic transfer, separately labeled

The order certificate admits a literal finalizer simplification, independent of any universality claim. Let the source residuals be F_0,...,F_23. The eight sign-product indices are `1,3,11,13,15,17,19,21`; they have the form u*v with natural coordinates. Replace their squares by the products themselves, retaining the other sixteen squares. This preserves the complete natural zero set and its unique tuple, stays nonnegative on the entire real nonnegative orthant, retains degree four, and has 289 expanded monomials. In a schedule evaluating the same residuals first, it saves exactly eight multiplications used for squaring; the reduction is in the finalizer, not a claimed optimized total circuit count.

If only natural-zero equivalence is required, also leave the two parity residuals (indices 5,7), `e(e-1)`, unsquared. They too are nonnegative on natural inputs. This variant has fourteen squared residuals and ten raw residuals, degree four, 287 monomials, and saves ten finalizer multiplications. Coordinates and all natural zero sets remain unchanged.

For either selected set I, the exact identity is

`P_original - P_reduced = sum_{i in I} (F_i^2-F_i)`.

The script verifies this as an equality of complete sparse polynomials, not only by sampled zeros. It additionally checks 1,500 signed and 1,500 natural supplied assignments for each formula and four canonical zero fixtures. The stronger natural-only variant actually loses real-orthant positivity: all unspecified coordinates zero, set `a=1/4`, `p=1/2`, `xlower_plus=1/4`, `p_rem=1/2`. The old polynomial is 1/16 and the ten-term reduction is -1/4. Thus its positivity scope must not be widened. No supplied witness is removed, no universal monoid is instantiated, and no 87-operation bound is lowered.

## Exact executable evidence

Both author commands are `python code/verify.py`, run from private package copies. The parallel verifier rewrites `data/verification_counts.json`; its stdout contains Python version and elapsed timing, which are not semantic receipt fields. The order verifier normally recomputes and compares its bundled deterministic receipt. All five original JSON artifacts across the packages remained byte-identical. The parallel example CLI `python code/parallel_certificates.py` also reproduces its bundled JSON byte-for-byte, before and after repair.

Original author results include 160,524 threshold assignments, 32,805 complete small polynomial assignments, 64 consumption matrices, 38,496 one-coordinate mutations and 328 history/first-halting cases for parallelism; 60,549 profiles across 180 multiplicity boxes, 9,841 normalization words, 23,128 profile decisions, 4,460 mutations and 2,000 matrix products for order. All passed.

Additional independent checks recorded in the portable review receipt:

- 6,000 guarded/flat/retention extent candidates against an independently written operational oracle, including 519 constructed roots and 1,557 joint witness mutations; 7,000 arbitrary natural full assignments and 200 rational orthant assignments.
- 24,576 full supplied Boolean witness tuples for guarded ordinary/flat one-species certificates, yielding exactly eight expected roots; 115 independently enumerated history zeros and 160 horizon/count ledgers.
- Every ternary word of lengths nine and ten: 78,732 words, with direct position-pair counting; 5,797 complete interval slices and 833 c=2 corner slices.
- 300 longer normalization words and 11,688 checked vertices; 9,936 joint two-witness variations over four canonical cases; 388 malformed profile/environment/coefficient inputs rejected, plus deep polynomial input ownership.
- Both complete sparse finalizer identities and the tests described above.

These are bounded source and implementation checks. They do not exhaust all unbounded witness spaces; the general conclusions rely on the reviewed proofs.

## Primary-source cross-check

Targeted source checks support the report's framing, without a priority claim:

- [Alhazov–Verlan, arXiv:1009.2706](https://arxiv.org/abs/1009.2706): author abstract explicitly supports computational completeness and the published 23-rule system. The full 23-rule table was not independently compiled here; no current minimality claim is made.
- [Woods, Theorem 1.10 and Definitions 1.6/1.9](https://arxiv.org/html/1211.0020v2): finite Presburger counting implies piecewise quasipolynomiality and a rational generating function. Fixed-horizon finite fibres meet those hypotheses; one parameter yields an eventual residue-polynomial form.
- [Valiant's original paper, pp. 410–414](https://www.math.cmu.edu/~af1p/Teaching/MCC17/Papers/enumerate.pdf): oracle reduction convention and monotone 2-SAT counting baseline were checked. The report's Turing-completeness qualifier is appropriate.
- [Rigo–Salimov's author record](https://orbi.uliege.be/handle/2268/178703): the definition of binomial equivalence agrees with scattered-subword counts. [Teh's author abstract](https://arxiv.org/abs/1506.06476) supports the Parikh rewriting/counter background; neither was used as a substitute for the report's self-contained interval proof.
- [Roman'kov's author abstract](https://arxiv.org/abs/2209.14786) states a fixed finitely generated submonoid with undecidable membership in a sufficiently large finite Heisenberg power. [Shafrir's author abstract](https://arxiv.org/abs/2405.05939) has the commutator Hirsch-length-one/two restrictions quoted by the report. Those ambient hypotheses do not cover arbitrary Heisenberg powers, and the report says so.

The flat-maximal DOI redirected to an inaccessible publisher page during this review. I did not independently re-audit that paper's full model or historical open questions. The report defines and proves its own flat semantics rather than depending on an uninspected operational identification. No literature novelty or still-open status is certified here.

The batch replay entry point is [incoming_substrate_review_808b53ed8.py](incoming_substrate_review_808b53ed8.py); it extracts original archive bytes and applies the patch to a private copy.
