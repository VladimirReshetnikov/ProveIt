# Incoming comparison for round twelve

Reviewed main: `9a33342a03d19cf5b061b2083c6b5d3f27f752ed`, 2026-10-24 01:38:36 UTC. Baseline: `2605669a532342f153b13eb6b4a0af4b54f5fa37`. The complete GitHub comparison response covered ten intervening commits and changed paths; the redundant raw response is omitted from the compact release, while this summary and FETCH_LEDGER.json retain the findings and authentication. The latest catalogue still ends at75; six incoming archives have not yet been placed. All 26 fetched resources have exact Git blob SHA-1 authentication and SHA-256/length records in `FETCH_LEDGER.json`. All six archive CRC inventories and relative member paths passed. No upstream executable was run.

## Main findings

1. The repository itself now supplies a materialized nine-positive circuit at **440 operations, degree1,845,940**, down from443, by reusing M*U, C*D and rank+1. The nonnegative-coordinate version has447 operations. This preserves the polynomial exactly, not merely its zero set. The candidate is under `current/Computability/DiophantineConsistency/candidates/gap2082-shared-products/`. Its coefficient binding is a repository-relative pointer to an older candidate, not a payload vendored in this review directory.
2. Joint Guards supplies **25 unrestricted integers/degree8**, **23/12**, **22/16**, **21/20**, **20/32**, **19/88**, with127,121,118,115,112,109 live binary operations respectively. It also supplies37/4 and31/6; round11's30/6 remains better. The joint positivity lemma combines determinant positivity with eta*zeta positivity into one nearest-square certificate. All six lower-variable endpoints arise by exact polynomial restoration; the deepest eliminatesV,I,a,E,eta. The four auxiliary sign coordinates remain.
3. Centered Pell Norms supplies **24 integers/degree10**, **22/14** (123 operations),23/12 (122 operations),26/8 (131 operations),31/6 (144 operations). It centers both first and auxiliary Pell roots, and performs reversible norm row reduction using a scale independently forced nonzero. The Radical Guard Descent packet also attains22/14 and23/12, with differently centered coordinates and no optimized integer operation claim.
4. Joint Guards supplies **11 positive variables/degree257/114 operations**. The lower-cost277/111 endpoint is duplicated independently in all four full new research packages and round11. The257 construction centers atV before transporting the auxiliary root, and bootstraps C>0 without assuming the transported gap's sign. This is a genuine degree/cost tradeoff.
5. Radical Guard Descent supplies **nine positive variables/degree1,158,228/1,753 operations**, a new least-degree point, by a654-term polynomial majorant of the entire radical. Its operation count is far larger than440. This is not a uniformly simpler equation.
6. Budget and Centering and Centered Pell Norms supply12positive/78/103; our round11's78/101 remains smaller at equal degree. Budget supplies24Z/10 and23Z/16 but the newJoint Guards andCentered endpoints dominate these variable/degree points.
7. The anomalous `report.zip` consists ONLY of `report.tex`. It claims **12positive/70/100** and **9positive/1,158,240/811**, but none of the promised literal graphs, coefficients, or verifiers are in the archive. Its12positive theorem/formula is explicit enough for fresh reconstruction; do not claim the100-operation artifact was audited. The9positive report is less complete: it describes a majorant construction whose external graph is absent. These points should be labeled manuscript-only until independently materialized.

## Unrestricted-integer frontier after combining these arrivals and round11

Keeping variable-count/degree Pareto points, not claiming minimum circuits:

|Variables|Degree|Concrete source|
|---:|---:|---|
|37|4|Round11; Joint Guards|
|30|6|Round11|
|25|8|Joint Guards|
|24|10|Budget and Centering; Centered Pell Norms|
|23|12|Joint Guards121ops; Centered Pell Norms122ops; Radical Guard Descent|
|22|14|Centered Pell Norms123ops; Radical Guard Descent|
|21|20|Joint Guards115ops|
|20|32|Joint Guards112ops|
|19|88|Joint Guards109ops|
|10|1,245,324|Round11,480ops|

22/16 remains useful as a lower-operation alternative118ops, though22/14 dominates in variable/degree alone. Additional historical13-integer and other high-degree operation tradeoffs remain in the catalogue; the table is not an exhaustive cost/degree/coefficient Pareto classification.

## Paths worth reading immediately

All paths below are relative to `arrival/`:

- `ZFC_Diophantine_Joint_Guards_2026-10-24/ZFC_Diophantine_Joint_Guards/joint/PROOF.md`: common-sign compression and19-variable monic restoration chain.
- Same root, `pell/CENTERED_PROOF.md`:11positive257 construction and noncircular bootstrap.
- Same root, `certificates/INDEX_FREE_CRT.md`: removes encoded index and one variable-power graph, but does not finish ordinary-polynomial compilation.
- `con-zfc-centered-pell-norms/con-zfc-centered-pell-norms/integer/PROOF.md`:22/14,24/10.
- `con-zfc-radical-guard-descent-2026-10-23/con-zfc-cross-guard-descent-2026-10-23/nine_positive/`: literal654-term majorant and final9-variable DAG.
- `report/report.tex`, lines428–635: ordinary rather than normalized strong norm,12positive degree70. Completeness replaces multiplier i by Delta*i; it does NOT divide arbitrary i byDelta.

## Formal proof status and research direction

Main now proves local internal Euclidean division, conditional/list-head semantics and smaller shared-row syntax constructor graphs. The actual fork graph uses3 auxiliaries and4 quadratic rows, and shared syntax compilation gives4*forkCount auxiliary witnesses and4*forkCount+1 rows. This does not materialize a full proof-checker consistency polynomial. Native high-mask support and local masks advance; arithmetic coefficient-interface binding, global tableau calibration, converse completeness and final internal consistency theorem remain open.

Commitf50e5ae7 explicitly pauses Lean work in favor of smaller complete equations. None of the new incoming packages closes the full encoded internal-ZFC proof gap. They claim ordinary mathematical compositions of explicitly inherited native/compiler/calibration results, with finite algebra/data tests, not a new Lean/Rocq consistency-equation certificate.

The independent direct sources in these packages converge on coefficient-height budgets to replace common-multiple blocks; they remain uncompiled. Hence merely suggesting that architecture would repeat existing proposals. Materializing its global polynomial, removing additional sign auxiliaries without a hidden rationality failure, or replacing the native source with an actually completed smaller fixed source would be genuinely new relative to this intake.

## Independent checks completed here

`check_literal_counts.py` is newly authored and reads JSON as inert data. It checks declaration topology, backward liveness and live binary operation counts on16 literal DAGs, plus crude degree upper bounds where names permit. It passes normal and optimized Python. It does not import any upstream module. `LITERAL_COUNTS.json` records the paths, file hashes, variables, live counts, degree claims and dead nodes. This check is NOT a semantic equivalence proof or an exact-degree proof. Archive hashes authenticate provenance, not correctness of upstream mathematical claims.

Our round11 upload exactly matches the previously delivered ZIP SHA25683bccd59ab691f7076a36c2b03cf84f05f8f7b2c04490ede94c389c29ec2034d.
