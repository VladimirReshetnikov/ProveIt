# Bounded independent intake of the planar four-particle report

**PASS within the stated scope; no error found.** Report31 gives a fixed binary planar cellular automaton with an explicit mass-four shuttle orbit and a local quartic certificate. It gives no universal machine simulation or lower complete universal Diophantine operation bound. Its 614 auxiliary coordinates must not be compared directly with Report28's 1,494-witness whole-endpoint example: they certify different relations.

The archive is [Binary_Planar_Four_Particle_Shuttle_Package.zip](../../../../../docs/incoming/Binary_Planar_Four_Particle_Shuttle_Package.zip), SHA256 `08020df876af26b1c8cfbf42aa2a79386375254f573f2e5079c07263689d7d98`. The [independent standard-library checker](review_binary_planar_four_particle31.py) reads ZIP members as data only; its [receipt](review_binary_planar_four_particle31.json) records exact reconstruction and bounded orbit checks. No archived Python, launcher, verifier or historical suite was executed.

## Pinned scope

The following members, under `binary-planar-shuttle-release-20261003/`, were authenticated:

| Member | SHA256 |
|---|---|
| `README.md` | `c9202b6629735360706cdb8d9164a93af034fbd52a1bca18bb0fe9edfc59046d` |
| `scientific/PROOF.md` | `a10c07b450ad16bd1591091c4dc4c0b241ccb00d99fb58f1a77a2e200752a373` |
| `scientific/LOCAL_ALGEBRA.md` | `6aaad6679b2ba8cd5fd183203a62a054a8b9defdf9a6b29df94cb65ac18acf60` |
| `scientific/audit/drift-and-first-arrivals.md` | `32b7fe7cde1a48d25fbe88023661af0d071a498e2b6646833550b9b9b2658029` |
| `scientific/local-rule-certificate.json` | `92d4f4265004704c44bbf5d53d1e0d61e29ce1c923d7720a4293b8bb2d2ced8c` |
| `scientific/local-quartic-certificate.json` | `e0d9bd288b86e2d3c521a7e40c5945707e61825f992f1741bc5d64be0ae11613` |
| `verification/expected-quartic-counts.json` | `d4cf053e5fe09ac952717f99186d16642d587705655eb93a2484c05031e7daee` |

The three mathematical notes and README were read in full. Their all-input and parameterized proofs were assessed directly. The original archive code/API, PDF rendering, provenance tooling and reported exhaustive suites were not audited or rerun. Attribution of the one-dimensional patterns to Report12 and comparisons with Report30 remain inherited historical context; neither is needed to verify the four explicitly stated planar replacements here.

## Geometry, all-input scope and orbit formulas

The component-recognition proof is sound. Each recognized component has an exact finite radius-two halo. A fragment of an infinite component cannot falsely pass: a path leaving the proposed component has a first occupied site inside that halo. Each replacement has an explicit displacement-at-most-one particle bijection. Distinct original components have mutual distance at least three, so their outputs cannot collide, including against frozen components. This proves finite mass conservation on arbitrary malformed inputs, with a well-defined bounded-displacement correspondence on infinite inputs. It does not prove reversibility, and none is claimed.

The stated phase intervals handle both collision boundaries, including k=7. One cycle takes `2(k+n)−10` steps, giving `T_n=n²+(2k−11)n`. The visited rows omit both x=1 and x=k+n−1; the stationary centered-box count correctly subtracts both families and handles N=k−1 separately. Its leading coefficient is1/2. The first-arrival formulas also correctly distinguish the initially present right marker on row zero.

For the drifted rule, translation covariance gives `F^t=translation_(0,t) G^t`. The proof that all four trajectories are disjoint is valid. The bulk and marker skipped heights are respectively

    a_n=n²+(2k−10)n−1, n≥1,
    b_n=n²+(2k−9)n+k−5, n≥0.

They interlace, so the exact box formula beyond the correctly retained cutoff N≥k+1 has increments between one and four. This justifies both `C_F(N)=4N−4sqrt(N)+O_k(1)` and its generalized inverse `M/4+sqrt(M/4)+O_k(1)`, including integer rounding. The weaker cutoff N≥k would indeed miss the first lifted marker's horizontal coordinate.

The new checker independently simulates the four component replacements for k=7,8,11. It checks 483 phase states, 183 first arrivals and 261 stationary/drifted box calculations. This is small corroboration of the parametric proof, not an exhaustive full-shift search.

## Local algebra reconstructed independently

Starting only from the four printed input/output shapes, the checker rebuilds all sixteen signed recognition indicators and all32 exported G/F cylinders. It then reconstructs the exact614 multiplication-chain instructions, every one of the693 residual polynomials, and their entire sum-of-squares expansion. The saved3,403-term integer polynomial agrees coefficient for coefficient.

The six translated L halos are distinct45-variable sets; their leading coefficients cannot cancel. Their union is precisely the78-cell rectangle `[-6,6]×[-3,2]`. This proves Boolean degree45 and essential dependence on every cell; uniqueness of multilinear Boolean interpolation then gives exact centered radius6. The drift merely translates the rectangle to `[-6,6]×[-4,1]`, retaining exact radius6. These are properties of these particular rules, not global minimality results.

The independently reproduced ledger is79 external coordinates,614 natural auxiliaries,693 squared residuals,1,990 residual-monomial occurrences,6,032 ordered expansion contributions,3,403 collected monomials, maximum absolute coefficient2, and exact quartic degree4. Each input-bit residual forces a binary external value; each acyclic product equation uniquely forces its next auxiliary; the final equation forces the output. This proves zero-or-one fibers over both natural and real auxiliaries for this one local transition. Mutation tests are not needed as a substitute for that triangular proof.

## Comparison with Reports26–28 and arithmetic consequence

Reports26–27 concern a source-uniform one-dimensional five-particle simulation, two full-shift involutions, and an evaluator including prospective rediscovery on malformed supports. Report28 pays a fixed-horizon whole-configuration endpoint circuit, whose arity grows with the chosen horizon. Report31 instead fixes one two-dimensional shuttle rule and certifies one output bit from78 local input bits. It neither implements nor replaces the earlier source compiler or its whole-orbit verifier.

The614 product-chain auxiliaries are not a complete elementary-operation count for evaluating the quartic: residual formation, squares, additions and any shared complements would also have to be charged. Exact Boolean degree45 and quartic degree4 measure different representations. No arithmetic saving follows from comparing these numbers or from the reduction to four particles in a different spatial dimension.

The specified shuttle family has explicit timing and reachability formulas. This does not establish universality of the rule on other inputs, nor a uniform simulation theorem. A growing space/time unfolding would still require a new unbounded-history encoding and ordinary-input interface before it could affect fixed-arity universal Diophantine bounds. Local unique witnesses give no general finite-fold halting representation. The current74/85 operation bounds are unchanged.

Fresh exact receipt replays from `/`, normally and under `python3 -O`, passed:

    python3 /absolute/path/review_binary_planar_four_particle31.py --repo-root /absolute/path/Proofs --expect /absolute/path/review_binary_planar_four_particle31.json
