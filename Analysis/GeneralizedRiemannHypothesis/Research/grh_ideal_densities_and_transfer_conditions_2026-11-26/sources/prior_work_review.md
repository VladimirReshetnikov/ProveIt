# Review of prior GRH-transfer reports

Assessment date: 26 November 2026. ProveIt is pinned to
`5cc267af75a635199ac5d93a7d49cbce521daefc`. The incoming directory contains
46 ZIP archives and one README. All 46 ZIPs were downloaded at that commit,
checked against their Git blob SHA-1 and byte size, and assigned SHA-256
digests. This verifies source identity, not mathematical correctness.

The comparison pin `48efe71a726dddc5a505534edaa4c0fd190416b9` contained 41
ZIPs. Exactly five archives were added after that pin; no surviving file
changed its Git blob:

- `grh_beyond_dirichlet_2026-11-25.zip`
- `grh_method_transfers_graph_towers_and_finite_rings.zip`
- `grh_transfer_bridges_2026-11-25.zip`
- `grh_transfers_cycle_signings_and_lubin_tate.zip`
- `grh_transfers_density_gaps_and_zero_tests.zip`

The machine-readable inventory is `archive_inventory.csv`. The original
GitHub directory metadata and exact archive checks are retained in
`inventory.json`, `inventory_previous_48efe71.json`, and
`archive_verification.json`.

## What was actually reviewed

The corpus was inventoried in full. Introductory summaries were inspected
for the principal research lines. Detailed mathematical reading in this
review concentrated on:

1. `grh_transfers_density_gaps_and_zero_tests.zip`: the complete natural
   versus upper density arguments in `integers.tex`, `integer_more.tex`,
   `natural_density.tex`, and `gap.tex`.
2. `grh-progression-densities-and-cubic-prime-race.zip`: the complete
   `progressions.tex`, especially the finite valuation-cube exchange and
   the single-prime upper-density construction.
3. `grh_method_transfers_2026-11-25 (2).zip`: the full K-theory section and
   exact Bernoulli/dimension checker. The checker was rerun with `--ranks`;
   all its assertions passed.
4. `grh_exact_torsion_transfer_2026-11-25.zip`: the full K-theory source
   audit distinguishing the short proof from the original strict-Selmer
   interface.
5. The assessment and README material for the bridges, sparse CM,
   exponent-seven, graph-tower, Lubin--Tate, synthesis, structural, and
   early source-audit packets.

This was not a fresh proof audit or complete computational replay of all
46 manuscripts. Claims below attributed to those manuscripts remain prior
claims except where the present report supplies its own proof or an
explicitly identified fresh computation.

## Current frontier and what must not be presented as new

| Line | Prior archive(s) | Existing result or reduction | Remaining issue |
|---|---|---|---|
| Geometric progressions in polynomial rings | `grh-progression-densities-and-cubic-prime-race.zip`; `grh-methods-polynomial-density.zip` | Natural-density gain over the greedy set for polynomial ratios; upper-density gain for rational ratios; reported disproof of Asada et al. Conjecture 6.3 by finite exponent constructions | Exact extremal values and rational-ratio natural-density optimality |
| Natural versus upper densities | `grh_transfers_density_gaps_and_zero_tests.zip` | Strict gaps over the integers for both ratio conventions and over every finite-field polynomial ring; computability and attainment statements | Natural rational-ratio greedy optimality; comparison of the two natural-density optima |
| Tiny explicit polynomial-ratio margin | `grh_beyond_dirichlet_2026-11-25.zip` | Revalidates the earlier counterexample and improves its binary margin to `2^(-2^476)` using variance | This is already inherited work; it is not the latest general density frontier |
| Singular moduli | `grh_sparse_singular_moduli.zip`; `grh_transfer_bridges_2026-11-25.zip` | Claimed five-term classification; exact support seven for the powered families at discriminants -87 and -152 | The global six-term threshold for unpowered singular moduli |
| Prime-conductor CM density | `grh_transfers_singular_moduli_and_symmetric_powers.zip` | Full-support lower density above 99.9818260107372245% for Gaussian prime conductors; optimal symmetric-power test polynomials | Full-support statement for every conductor; new analytic bound for symmetric-power RH |
| Class-group censuses | `grh-exponent-six-and-transfers.zip`; `exponent_seven_and_grh_transfers.zip` | Claimed complete exponent-six census of 432 fields/1,236 orders and exponent-seven census of 33 fields/40 orders | Further exponents; these are not new in the present analysis |
| Nonabelian zero criteria | cyclic-generator, Sylow, A6, PSL2, reflection, relative-race, deficit, and sharp-transfer packets | Explicit character weights and one-sided prime-sum criteria for several nonabelian groups | The arithmetic covolume/divisibility/spanning estimate for the actual new weights |
| Nonabelian local lattices | `grh_nonabelian_transfer_2026-11-25.zip`; synthesis | An optimal integral frame bound 229 for the real S3 example, unramified cubic transfer, projective frame constructions | Uniform global cohomology, lattice-level and prime-spanning estimates |
| Torsion selection | exact, sharp, fixed-field, quantitative, research, graph-tower, and cycle-signing packets | Multiple sharp obstruction/selection formulas, formal-group and Lubin--Tate extensions, finite tolerance computations | Do not reannounce the sharp cyclotomic shell bound as new |
| K-theory | exact-torsion; method-transfers (2) | Precise branchwise certificate logic; Bernoulli unit screens through degree 160; K124/128 comparison-space dimensions; small Hecke reconstructions | Exact strict-Selmer transfer/coverage for the chosen route and large determinant certificates |
| Other claimed completed applications | `dirichlet-grh-research.zip`; graph-tower and cycle-signing packets | O'Hara/heavenly-curve results, prescribed progression spectra, graph signings and valuation results | These are prior-report claims, not completed independent verifications here |

## Scope of the new ideal result

The present construction extends the polynomial valuation-cube exchange
to nonzero integral ideals in *every* number field. The new uniform
observation is that the divergent product of `1+1/Norm(P)` eventually
dominates the convergent product of the local greedy positive-orthant
weights. It supplies a finite rational stopping certificate and proves a
strict natural-density improvement for integral-ideal ratios. It answers
the existence portion of Best et al., Question 5.1, and goes beyond the
quadratic case. It does not solve the fractional-ideal natural-density
Question 5.4.

An independent second argument establishes a strict gap between the
optimal natural and upper ideal densities under each ratio convention.
Its finite witness is the replacement of exponent set `{0,1,3,4}` by
`{0,1,3,7,8}` in one pure prime-ideal fiber. The crucial norm-tie argument
is valid: writing an excluded exponent v in ternary, let a retain exactly
its 1-digits and b retain both its 1- and 2-digit positions as 1-digits.
Then a,b are greedy and v=2b-a, with a<b<v. Coordinatewise this constructs
two strictly smaller-norm greedy ideals blocking every nongreedy ideal.
Hence optimizing every norm prefix would uniquely force the greedy set,
which the five-point fiber disproves at a later prefix.

No matching all-number-field ideal-density statement was found by the
targeted text scan of the 46 archived manuscripts. This is a scoped
comparison, not a proof of worldwide novelty. The primary literature
search located the explicit questions in Best et al. and the integer
precedents of McNew.

## K-theory: verified preparation and the actual missing work

The fresh replay used
`grh_method_transfers_2026-11-25 (2)/grh_method_transfers/code/verify_ktheory_prefilter.py --ranks`.
Its 84 generalized Bernoulli values matched two independent exact
rational formulas; all fourteen Bezout/gcd certificates and all recorded
invariant-space dimensions passed. For degrees 124 and 128 the common
numerator gcd is 4. The negative comparison-space dimensions are,
respectively, 550/1240 and 605/1360 for the two standard stabilizers.
These are exact finite computations, not K-group vanishing theorems.

The short source's `shaOdd` bound selects the wrong conjugation sector
for the direct rational even-twist restriction used in the K_{4m} route.
The stronger pointwise strict-Selmer interface studied by the K-theory
papers is in the original, much larger source archive. A common witness
at every Frobenius probe cannot be inferred from a pointwise existential
witness statement. For branch-varying probes the basic exclusion
certificate takes a product over branches *before* a gcd over probes.
The arithmetic coverage of every admissible witness and the integral
Hecke normalization must be justified before this integer test applies.

Current primary preprints distinguish two routes:

- Pintar, Hexagon 2611.00829v3, explicitly conditions vanishing through
  degree 104 on the Step 17 arithmetic construction and invokes a common
  representation extraction from a separate research archive.
- Mok--Zheng, Hexagon 2611.00998v1, claims unconditional vanishing through
  degree 120 using pointwise witnesses and additional transfer arguments.
  Its provenance states that the modified Gaussian Lean entry point has
  not been fully rebuilt.

An unperformed Lean rebuild alone is not a proof gap in a written
mathematical proof. The justified statement here is that the extra
bridge is not exported by the inspected short repository and has not
been independently verified in this analysis. The proposed new ideal
theorems need none of these K-theoretic claims.

The current source audit also identifies a saturation lemma upgrading a
finite-level Selmer length bound below the coefficient precision to a
divisible-coefficient bound for the same twist. Therefore the blanket
"finite precision makes the full bound unavailable" objection in some
earlier prose should not be carried forward; exact hypotheses and local
conditions remain essential.

## Primary references located

- A. Best et al., *Geometric-progression-free sets over quadratic number
  fields*, Proc. Roy. Soc. Edinburgh A 147 (2017), 245--262,
  DOI https://doi.org/10.1017/S030821051600010X;
  https://arxiv.org/pdf/1412.0999. Section 5 gives Questions 5.1,
  5.3--5.5. In particular 5.4 asks about natural density for fractional
  ideal ratios; a limsup construction alone does not answer it.
- N. McNew, *On sets of integers which contain no three terms in
  geometric progression*, Math. Comp. 84 (2015), 2893--2910,
  https://arxiv.org/abs/1310.2277. The finite-exchange precedent is
  Theorem 3.3; the natural/upper density questions are in Section 7.
- M. R. Murty and J. Van Order, *Counting integral ideals in a number
  field*, Expositiones Math. 25 (2007), 53--66, Theorem 5,
  https://doi.org/10.1016/j.exmath.2006.08.001;
  https://www.math.uni-bielefeld.de/vanorder/count.pdf.
- C. P. Mok and H. Zheng, *Vanishing of K_{4m}(Z) through degree 120*,
  24 November 2026, https://hexagonmath.org/2611.00998v1.
- L. Pintar, *Vanishing of K_{4k}(Z) through degree 104 from Alpöge's
  Step 17*, https://hexagonmath.org/2611.00829v3.

The search scope was the named ideal/progression papers, exact question
terminology, the two current K-theory preprints, and relevant earlier
ProveIt archives. Absence of another located theorem is not a priority
certificate.
