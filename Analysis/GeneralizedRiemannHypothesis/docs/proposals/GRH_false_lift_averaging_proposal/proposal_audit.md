# Nonduplication audit

Source: [ProveIt proposal archive](https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/GeneralizedRiemannHypothesis/docs/proposals), inspected through GitHub on 27 November 2026. Eighteen subdirectories were returned. Recursive tree listings were not truncated. Principal TeX headings/abstracts and targeted full-text scans for bottom-of-tower declarations, hyperplane sums, false lifts, factorial and coinvariants were reviewed; the existing order-test proposal's detailed audit of the earlier five-directory collection was also consulted. This is a targeted overlap audit, **not** a complete proof audit or a claim of global novelty. The main branch was observed at `9050b04000647d588d0c78d945180abcd3b0bcf7`; the target file, guide and periods file were separately confirmed at that revision. Proposal blobs below identify the versions read from `main` (not all re-fetched at the pinned commit).

| Proposal directory | Principal change | Relation to this note |
|---|---|---|
| centered_theta_lift_simplification | Centered covariance, direct ramified-source rank recurrence, adaptive completion | Different upper/spanning branch. |
| cm_norm_theta_simplification | Four-copy norm cancellation for local derivative sharpness | Different lower local coefficient estimate. |
| cyclotomic-interpolation-and-theta-lifts | Uniform cyclotomic grid torsion choice and near-spanning | Different twist choice and spanning. |
| discrete_hecke_simplification | Signed lattice Pieri count and saturation of bad Smith directions | Different local divisibility estimate. |
| edge_hecke_simplification | Integral orbit trace and direct exceptional-divisor bound | Different invariant-average operator; not descent pairing. |
| gram_adjoint_simplification | Integral Gram duality and adjoint norm, removes frame counting | Explicitly retains false-lift orthogonality; this proposal simplifies the retained theorem. |
| grh-class-count-finite-quotient | Counts adelic inverses modulo a finite quotient | Class-counting, not test-function representation. |
| grh_order_tests_2026-11-27 | Norm/order tests for distinguished finite labels | Supplies good types, not the bottom descent theorem. |
| newton_torsion_simplification | Newton divided differences and same-order torsion sampling | Different Selmer specialization step. |
| orbital_theta_exchange | Canonical scalar twisted coinvariants and complementary primitive-frame matching | Closest general technique, but different theorem and output; see below. |
| proof_simplifications | Short twist selection, Perron inversion, rank recurrence | Different analytic and spanning interfaces. |
| rh-simplifications | Sharp rank deficit, cyclotomic interpolation, quadratic sieve, endpoint | Different interfaces. |
| rh_sparse_theta_proof | Sparse cutoff grid, reciprocal convexity, local averages, good-twist selection | Different analytic interfaces. |
| rh_two_order_tests_proposal | Two power tests and subgroup exclusion for finite labels | Different local label hypothesis. |
| robust_theta_labels | Three power tests, scalar-order weakening and bad-type count | Different local label hypothesis. |
| shorter-theta-lift-proof | Short correlations, Poisson completion, mollifier, centered recurrence and PNT | Different analytic/spanning interfaces. |
| signed_theta_gain_simplification | Signed product formula and determinant normalization-free comparison | Does not establish false-lift orthogonality. |
| theta-lift-simplifications | Flag-adapted row clearing, finite labels and paraboloid sparse places | Uses orthogonality in projection bound, does not replace bottom theorem. |

### Closest overlaps

The `orbital_theta_exchange/orbital_theta_exchange.tex` abstract and Section 3 (lines around 34, 106, 144, 280) use finite averaging to establish **scalar** twisted coinvariants for matching complementary column/row data. This is a common method, not a newly discovered averaging technique. Assume that method and any generic finite-orbit support helpers will be implemented. The distinct contribution here is to average a general test function with **values in the orbit span of a form**, under a larger triangular group, use hyperplane annihilation to prove absence of stabilizer invariants on the bad locus, and decompose compact support into block-datum orbits. There is no complementary frame matching or exchange partner. The exported bottom-of-tower theorem, rather than an exchange identity, is the target.

The `gram_adjoint_simplification/gram_adjoint.tex` abstract and lines around 39 and 206 explicitly retain orthogonality to false lifts via `isOrthogonalToFalseLifts_glue_periodLift`; this note shortens a prerequisite to that theorem. The row-clearing proposal in `theta-lift-simplifications` likewise uses false-lift orthogonality as an input. Label proposals affect the route to hyperplane annihilation, not the deduction from that property. These proposals can therefore be composed at their stated interfaces.

### Principal source identifiers (Git blob SHA-1)

Paths relative to `docs/proposals/`:

| File | Blob SHA |
|---|---|
| centered_theta_lift_simplification/centered_theta_lifts.tex | 48053a8e8682e327ac6b2e607166c72c2042a5f5 |
| cm_norm_theta_simplification/report.tex | 8e8f14ee87528e949dd976b80776d0f2abdd398e |
| cyclotomic-interpolation-and-theta-lifts/theta_simplifications.tex | ed596f05ef8cc0d9e6563b10b6e38c0dc67483e1 |
| discrete_hecke_simplification/discrete_hecke.tex | 53ef64e9d16583f0d3039e3037e8dd4bb09b13b3 |
| edge_hecke_simplification/report.tex | f7fd6a0337f46b0ccb4cde5ad0077eb153d9eaaf |
| gram_adjoint_simplification/gram_adjoint.tex | d1ce355c7b95cd83a2af6dd4187098a0f477afe4 |
| grh-class-count-finite-quotient/report.tex | c52303f9fe264427fa90b4ce6273ecdf025afcb6 |
| grh_order_tests_2026-11-27/grh_order_tests/order_tests.tex | 7ac97dbdf258aad02498f58faa270ee69dd5a3be |
| newton_torsion_simplification/newton_torsion.tex | 702f032f548bfa57d35ae3975c5b5cd9f644b417 |
| orbital_theta_exchange/orbital_theta_exchange.tex | 9a41a032d2adb7981f03977e5e516dfee2685ae0 |
| proof_simplifications/proof_simplifications.tex | 9065f4264f406427a423bd69a31d5a33fbe131a1 |
| rh-simplifications/endpoint.tex | 261eeb7941a50b6f529810505ffabdddffac37a3 |
| rh_sparse_theta_proof/sparse_theta_proof.tex | d75a839b4f965bd286f3b4dd402aa25698dd7ee4 |
| rh_two_order_tests_proposal/two_order_tests/two_order_tests.tex | 6f145414f61102a622b3916ea4b8732e302262b4 |
| robust_theta_labels/robust_theta_labels.tex | 6984574abb0a84c8f44a83fab298354d78937748 |
| shorter-theta-lift-proof/shorter_theta_proof.tex | 90a7d890256e4d05b5e17328eb30afe4b4e4557c |
| signed_theta_gain_simplification/signed_theta_gain.tex | 6c675dddeb1d945eef61442d6d5aa60c372124b1 |
| theta-lift-simplifications/theta-lift-simplifications.tex | 89197fe9ded77efb5c08c846f73ecc93c110a61b |

The original guide source blob is `6fddbfae7c356b7251eb6eb5d8629c2f42e2e278`; bottom-of-tower blob is `b113ad2b09b23d465d369e727f9e584920c7e554`; periods file blob is `a999c4f8eb57526a9d8215bc5e8c0b423aaccfae`. See the linked source anchors in the PDF and implementation plan. No repository files are redistributed here.
