# Updated existing-proposal inventory and exclusion map

Latest reviewed proposal snapshot: `1a59f50680e470fb5269bbe70c06f974c95ad930` of `VladimirReshetnikov/ProveIt`.
Earlier review snapshot: `d417d0b5b08edd4f5f67224fd310add7f1618ca0`.
All directory paths below lie under `Analysis/GeneralizedRiemannHypothesis/docs/proposals/`.

## Review scope and change of baseline

The current corpus contains **26 directories and 79 non-attribution Markdown/LaTeX texts, totaling 1,057,880 bytes**. The companion `proposal_text_manifest_v2.json` records every file, Git blob, SHA-256, size and mathematical/document headings. We compared all unchanged reports with the previous inventory and read the six new mechanisms, including their theorem statements, implementation boundaries and relevant future questions. The closest competing reports were reviewed in detail. This is a source-grounded nonduplication review, not independent proof checking of every proposal and not a claim of literature priority.

The 61 texts present at both snapshots have identical Git blobs. Six directories and 18 texts were added; `robust_theta_labels` and its three texts were removed. **The removed proposal remains excluded from our novelty claim because it was already seen earlier in this task.** Its mechanism is recorded separately below.

Some readable Lean files also changed between snapshots. The target first-average source (`PathData`, `GridFirstColumns`, `FirstPath`) is unchanged. The manifest records all readable-tree changes; it does not claim whole-tree identity. In particular the `LabelsAndIndexTypes` update affects the good-label API, not the node-rank definitions used here.

## Main novelty decision

The canonical sweep, diagonal-only Fourier budget, exact endpoint cardinalities and broad active-frontier representation are **already proposed** in the latest corpus. Our original sweep/frontier draft is superseded as a novelty claim. A maximum-coordinate shell instead of a minimum-coordinate strip does not evade that overlap.

The distinct main proposal is now:

> After omitting the already-identified unused reflected initial coset, compute the stabilizer of the complete standard first-column tuple. It is exactly a product of the remaining false-column congruence kernels. Its order is independent of the twist. Evaluate the entire character-weighted transporter sum and normalize once, obtaining an initial path datum whose every value is zero or one root of unity, with coefficient budget **1**.

The contribution is the **specific anchored two-modulus stabilizer and its uniform cardinal**, plus the normalized datum and period-scalar consequence. Generic orbit averaging, character orthogonality and CRT are standard/reusable tools, not claimed as new methods.

## Complete current directory map

| Directory | Main report(s) and mechanism already proposed | Source-level boundary / exclusion |
|---|---|---|
| `centered_theta_lift_simplification` | `centered_theta_lifts.tex`: center the orbit covariance, act on ramified source directly, use actual missing-dimension completion cost, reduce translate allowance; optional products-of-contractions sampling proof. | `FewTranslates`, `SpanningTheorem`, `ShortAndEnough`, `LongForms`, `MainInequality`. It assumes the automorphic near-isometry and averaged second-moment inputs rather than reproving their trace formula. |
| `cm_norm_theta_simplification` | `report.tex`: replace rational-square cancellation by local CM norms; coefficient witness construction reduces twelve copies to four with same valuation bound; split/inert/ramified cases and zero-degree padding. | Local theta derivative sharpness and number of copies. Does not replace the original analytic theta/formal-group estimates. |
| `cyclotomic-interpolation-and-theta-lifts` | `theta_simplifications.tex`: uniform dimension-independent torsion selection by mixed-radius interpolation; simultaneous powers of one character; bounded-power-series variant; near-spanning at order `b^-4`. | `New/Congruences/Selmer/RootsOfUnity` and its selection callers, plus rank selection from existing near-isometry/second-moment estimates. |
| `discrete_hecke_simplification` | `discrete_hecke.tex`: signed integer-lattice enumeration replaces real Pieri-cone volume; permutation-cycle determinants and monomial orbit cancellation; saturation of bad Smith directions. | `PieriCone`, `DefectCount`, `ElementaryDivisorTheorem`; exact flag cancellation and power packing retained. |
| `edge_hecke_simplification` | `report.tex`: integral orbit trace plus scaled symmetric tensors for invariant-average contract; threshold Smith decomposition and low-rank perturbation for exceptional divisors. | `UpperBound/ElementaryDivisors/InvariantAverage`, part of `ElementaryDivisorTheorem`; keeps depth/root/defect inputs. Its orbit trace is not the automorphic second-moment trace formula. |
| `gram_adjoint_simplification` | `gram_adjoint.tex`: existing Weyl-Fock identity `GH=hI` directly makes the scaled adjoint integral; paired-conjugate norm estimate; optional scalar `n_aut h` in place of `n_aut h^2`. | `OneLift/LiftVolumeHeight` comparison operator and `ComparisonOperator/GluingMaps`; tight-frame construction and cardinality are targets. |
| `grh-class-count-finite-quotient` | `report.tex`: record Gram matrix plus ordered column classes of adelic inverse in `G^-1 R^r/R^r`; collision proves injectivity, determinant norm counts fiber. | `New/UpperBound/Size/ClassCount.card_stdClasses_le`; removes bounded strong approximation and extra bounded `GX` matrix while retaining constant. |
| `grh_diagonal_sweep_proposal` | `report.tex`, `LEAN_PLAN.md`: deterministic minimum-coordinate strips; diagonal-only cost `V^m`; exact column product `q^(mr+tm²)`; rank-sensitive first coset and last tuple cardinalities. Future questions include removing the one unused reflected initial coset. | Treat all sweep/count results and single redundant-coset deletion as already proposed. Does not evaluate all residual initial averaging fibres or normalize the whole datum to root-or-zero. |
| `grh_dual_fitting` | `report.tex`: finite annihilator and length duality give relative Fitting cost in one step; specialize relation lattice at zero and lift a determinant; exact row-lattice packing gives block determinant. | `Lib/General/Algebra/FittingIdealsAndLengths`, `New/Congruences/FirstOrder/FittingBlock`, `BlockFittingBound`. |
| `grh_exchange_sweeps` | `report.tex`, `LEAN_PLAN.md`: diagonal-only cost with existing induction, then deterministic strips; exact column counts; weight rescaling of triangular pairings and descents with two normalized chain laws and a Gram recurrence. Explicit further question asks for active-frontier path data. | Excludes canonical traversal, exact diagonal budget, broad frontier representation and normalized triangular Gram laws from the new contribution. No whole initial-average stabilizer computation. |
| `GRH_false_lift_averaging_proposal` | `false_lift_averaging.tex`: one finite vector-valued Reynolds average; stabilizers kill bad locus, finite good-orbit support decomposes into block data. | `OneLift/FalseLifts/BottomOfTower`, especially `descentsVanish_of_hyperplaneSumsAnnihilate`; replaces factorial shrinking cosets and local-constancy limit. |
| `grh_integral_field_presentation_proposal` | `report.tex`, `lean_plan.md`: common integral presentation for the cyclotomic–quadratic CM field via coprime discriminants; monogenic trace dual; explicit different phase; finite Frobenius-orbit model and nilpotent-sensitive congruences. | Auxiliary field arithmetic, different, local prime decomposition and partner congruences. Its ring CRT/orbit tools can be reused; it does not study the first-column gauge average. |
| `grh_order_tests_2026-11-27` | `grh_order_tests/order_tests.tex`: norm power tests plus one subgroup exclusion; elementary exact count and shorter union bound; smaller coefficient in bad-type inequality. | A further label weakening and counting proposal; compare all three label directories before claiming novelty. |
| `grh_real_samples_and_nearest_poles` | `report.tex`, `LEAN_PLAN.md`: nonnegative Taylor coefficients from finite differences of real transform samples; nearest-pole disk majorization; negative-residue real obstruction; real-only transform interface and targeted twist criterion. | Replaces the positive-measure abscissa argument in `IsPolar.landau`. Do not re-propose real-sample or nearest-pole analytic simplifications. |
| `newton_torsion_simplification` | `newton_torsion.tex`: minimal weighted Newton coefficient sampled by a tensor divided difference; harmonic averaging of successive Gauss-valuation drops; common primitive shell and singly exponential level ceiling. | Direct replacement for `New.Selmer.exists_rootsOfUnity_ellVal_eval_le_add`; unlike prior mixed-radius interpolation it uses one common exact primitive order. |
| `orbital_theta_exchange` | `orbital_theta_exchange.tex`: normalized orbital integrals, primitive-frame projection, finite certificate for twisted coinvariants; canonical matching on the entire full-rank Schwartz-Bruhat space. | `New/Determinant/Exchange/MatchingPartners`, `EquivariantDifference`, `TheoremForPartners`. Replaces symmetric coset representatives and artificial extension of finite summation. |
| `projective_incidence_grh` | `report.tex`, `LEAN_PLAN.md`: projective point–hyperplane intersection counts, positive-type normalizer-coset bound, Hilbert-valued incidence mixing, weighted corank tail. | Replaces finite-field Fourier/tensor estimates in `SecondMoment/PositiveType`; preserves the old compression-det bound. Its orbit fibres and character-free geometry are unrelated to the initial two-modulus gauge stabilizer. |
| `proof_simplifications` | `proof_simplifications.tex`, `fourier.tex`, `perron.tex`, `spanning.tex`: two short Dirichlet-polynomial selection tests; Heath-Brown quadratic large sieve; elementary character/Fourier completion alternative; direct smoothed Perron inversion at the far cutoff; stronger direct ramified-source rank recurrence. | Do not re-propose large-sieve good-prime selection, the elementary Fourier selector, far-cutoff contour shift, or direct use of ramified source in greedy spanning. |
| `rh-simplifications` | `sieve.tex`, `torsion.tex`, `spanning.tex`, `endpoint.tex`: quadratic large sieve; finite weighted cyclotomic interpolation; affine missing-dimension recurrence; explicit determinant-to-Landau assembly. | The endpoint explains ordinary positive-Laplace Landau with signed residues; it is not a separately stated new nearest-pole theorem. |
| `rh_sparse_theta_proof` | `sparse_theta_proof.tex`: reciprocal-coordinate convexity with a quadratic mesh loss; fourth-power cutoffs or fixed-chain dyadic block grid; reciprocal-window averages; logarithmic Gaussian second moment for twisted characters; a divergent good-prime subset criterion. | A sparse grid, average-at-cutoffs criterion, or weaker divergent family of admissible twists is already proposed. It explicitly rejects allowing the twist to drift with cutoff or omitting real-residue sign. |
| `rh_two_order_tests_proposal` | `two_order_tests/two_order_tests.tex`: two surviving order components suffice after Frobenius/power operations; weighted complement estimate rather than just witness mass. | Distinguished-label consumers, `IsCommonRootPower`, source projector and weighted bad-type bound. |
| `ribet_lattice_simplification` | `report.tex`, `LEAN_PLAN.md`: finite dual/Smith package for relative Fitting cost; determinant from the specialized row lattice with exact torsion term; direct full-rank block assembly without precision padding. | Polynomial relation-module and block determinant certificates; retain polynomial lifts and triangular scalar cost. No initial path-data normalization or theta averaging result. |
| `ribet_module_duality` | `report.tex`: identify functions with dual of finite evaluation module; direct triangular Fitting certificate and exact torsion-length cost; direct Cayley-Hamilton on a quotient, bypassing polynomial adjugate. | `FittingBlock.exists_mul_prod_X_mem_fittingIdeal`, `RibetMethod.exists_ribet_polynomial`, related matrices. |
| `shorter-theta-lift-proof` | `shorter_theta_proof.tex`: Jacobi Gram identity, elementary character estimates and smooth Poisson completion for twist selection; one-page large-sieve variant; direct ramified spanning; classical PNT cutoff route. | Analytic twist-selection alternatives and spanning from the existing moment inputs are covered. |
| `signed_theta_gain_simplification` | `signed_theta_gain.tex`: separate local divisibility gains from colength losses; compare one fixed determinant using signed local budgets; remove rounded global rational normalization. | Local-to-global upper determinant assembly and improved arithmetic remainder bound, preserving deep local estimates. |
| `theta-lift-simplifications` | Main report and `labels.tex`, `paraboloid.tex`: integral flag-adapted pivot basis; row-by-row clearing and compressed determinant; enlarged labels; explicit sparse infinite places via digit/paraboloid construction. | Projection-denominator row construction, finite-field labels, and sparse-place combinatorics are covered. |

## Removed but still excluded

`robust_theta_labels` was present at the earlier snapshot and is absent at the latest one. It proposed three explicit finite-field power/order tests, exact cyclic witness density, and preservation of the label consumers under Galois and power operations. It is not available as a “new” fallback merely because its directory disappeared. The earlier manifest retains its hashes and report structure.

## Closest overlap: what remains new after assuming the proposals implemented?

### Deterministic diagonal sweep

`grh_diagonal_sweep_proposal/report.tex`, §5, improves the initial count by retaining the exact number of initial coset families or bounding each group with its actual rank. It explicitly retains the averaging construction and its equivariance. Its final further-question list also identifies the one unused true initial coset and warns about twist-dependent normalization.

Assume both changes implemented. The remaining average still ranges over the false gauges at every level and the true interior quotient gauges. Our result identifies **all remaining fibres**, rather than only deleting the unused coordinate or tightening their cardinality bound. Backwards anchored-chain recursion fixes every observed quotient gauge, the two reductions fix the false initial gauge over the full grid ring, and only the interior false congruence kernels remain. Their character sum is zero or their cardinality times a phase. Normalizing by their fixed order gives budget 1. This is not supplied by the existing endpoint-count theorem or its redundant-node question.

The known diagonal transfer factor `q^(mr+tm²)` is then used as an input, not claimed again. Relative to the existing rank-sensitive bound, the new numerical consequence is removal of the **whole first-path exponent A**, leaving the terminal tuple exponent B and all class factors untouched.

A targeted search across all 79 current texts found the initial-average identifiers and suggestions only in this diagonal-sweep report/plan. The earlier `grh_order_tests_2026-11-27` audit also mentions less redundant scalar normalization as a generic opportunity, without an initial-gauge stabilizer, uniform-fibre theorem, or root-or-zero construction. That broad precursor is acknowledged; it is not the detailed result claimed here.

### Orbital theta exchange

`orbital_theta_exchange` supplies canonical local orbital sections and a finite twisted-coinvariant certificate for **complementary row/column matching**. It treats locally compact matrix orbits and Schwartz–Bruhat data and changes the local exchange interface. Its normalized orbital values need not be roots of unity; the report gives an example with a fractional normalized orbital integral. Its generic orbit/character tools can and should be assumed reusable here.

Our target is different: the finite product of all first-column gauge groups, with two coupled modulus reductions, both far endpoints fixed, and the initial true gauge tied by a block embedding. The needed new statement is the exact stabilizer product and its twist-independent order. Neither the orbital section theorem nor complementary-frame matching identifies that stabilizer or supplies budget 1 for `firstPathDatum`. We do not propose orbital averaging itself again.

### False-lift Reynolds averaging

`GRH_false_lift_averaging_proposal` averages a test function with values in the orbit span of a form under a larger triangular group. Hyperplane annihilation kills stabilizer invariants on a bad locus; compact good support is a union of block-datum orbits. Its target is the bottom-of-tower false-lift descent theorem, and it explicitly treats generic finite-orbit helpers as reusable from orbital exchange.

Our result uses a **scalar** weighted transporter to one prescribed standard tuple. It has no hyperplane-annihilation hypothesis, no form-valued orbit span, no good/bad-locus classification, no shrinking-neighborhood or compact-support argument, and no complementary-frame partner. Again, generic Reynolds/character summation is assumed available; the new content is the initial-column stabilizer calculation, uniform integer normalization and coefficient budget.

### Integral field presentation and projective incidence

The field-presentation report's CRT and Frobenius-orbit methods concern the ring of integers and prime decomposition of the auxiliary field. The projective-incidence report's fibres concern vector/covector lines in a finite-field representation under positive-type weights. Those tools may shorten generic infrastructure, but neither specifies or evaluates the first-column gauge transporter. No first-average theorem was found in either report or its plan.

## Secondary arithmetic-certificate cleanup

A separate optional extension replaces the existential multiset-of-roots certificate by algebraic integrality plus a uniform bound on complex conjugates, and flattens the terminal jointly invariant class sum before proving finite-place and archimedean estimates separately. No current report supplies that interface replacement or exact terminal joint contraction.

This should remain secondary, particularly after the initial budget becomes 1. The main theorem already gives the stronger root-or-zero certificate initially; there is no reason to weaken it before proving the normalization. The optional cleanup concerns the later Fourier transport and terminal proof scaffolding, preserves the existing numerical budget, and requires its own measured source scope.

## What the novelty claim must not say

- Do not claim the deterministic sweep, exact diagonal exponent or endpoint cardinal formula again.
- Do not claim the unused true initial coset was newly discovered.
- Do not claim generic weighted orbit sums or Reynolds averaging are new.
- Do not present the earlier finite-frontier suggestion as absent from the latest corpus.
- Do not infer a large source-line deletion from the numerical removal of the first exponent. A direct replacement construction may shorten callers, but a normalization lemma added beside old code may initially increase them.
- Do not claim the whole readable Lean tree stayed unchanged during the review or that the proposal has already been compiled.

The accurate contribution is a concrete, stronger normalization theorem for a specific average that the existing proposals leave in place.
