# Prior-report review: GRH method transfers

## Scope and evidence boundary

The source of this review is the 26 ZIP archives in `VladimirReshetnikov/ProveIt/docs/incoming` at commit `6fe2c1bd450aa7f19eab17fb9a6e76170b4fce00`. All were obtained from the checkout and inspected as data. The complete central-directory inventory, archive SHA-256 values, and extracted text-file paths are in `evidence/prior_inventory.json`. Text extraction used a path-traversal check and did not execute any archive code. The incoming README is an intake/governance document, not a summary of these GRH reports.

This is a substantive overlap audit, not an independent proof or certificate replay for all the earlier claims. “Proves” or “claims” in the table means the archive contains a written theorem/proof with that stated scope. Mathematical and finite-computation claims must stay attributed unless separately verified in the new report. Most prior authors explicitly disclaim worldwide priority and new Lean verification; one earlier general report includes separately compiled elementary Lean lemmas, which do not formally establish its downstream analytic applications.

## Executive finding

The earlier work has already explored most short formal/analytic transfers suggested by the proof architecture. In particular, fourth-power sampling, reciprocal-variable convexity, exact Jensen loss, positivity-class sharpness, positive-part Mellin criteria, L1/L2 averages, a linear auxiliary logarithmic window, finite combinations of errors, bounded-series torsion selection, infinite finite-budget packets, polynomial bounds for a fixed finite packet, determinant/Fitting transfer, and an odd cocycle comparison all occur explicitly. The reports also contain an extensive family of nonabelian zero-detection criteria, but none inspected establishes the corresponding new arithmetic covolume estimate. Repeating a new finite group or a slightly different prime weight is not by itself resolution of a new RH case.

Three strands should be kept separate:

1. **Exported-theorem applications:** Euler/idoneal and exponent-six classifications; norm-Euclidean fields; least primes, prime-generating constants and additive representations. These may be nontrivial new deductions or completed computations, but they use the RH endpoint rather than transfer the internal proof.
2. **Actual method transfers already on paper:** robust positive-part transforms, sparse scales, roots-of-unity selectors, determinant specialization, odd cocycle cohomology, and quantitative shell selection.
3. **Still-open arithmetic interfaces:** new Frobenius-sensitive geometric estimates, strict-Selmer/Hecke comparison, higher-order central-value nonvanishing with a real interpolation theorem, and coefficient-field/ramification control.

## Complete prior-work matrix

| Index | Archive | Main content present | Remaining interface / caution |
|---|---|---|---|
| 00 | `dirichlet-grh-research.zip` | Four papers: affirmative O’Hara finiteness deductions; uniform heavenly abelian-variety bounds for A4/A5 sextics; paired moving-height sharp Euler products and local mean square; periodic sets with prescribed rational-ratio spectrum built from weighted Behrend ideas. | The cubic finiteness argument is described as unconditional. The broader sextic arithmetic uses Dirichlet GRH and published local inputs, not new nonabelian GRH. New deductions are written proofs, not new Lean theorem checks. |
| 01 | `grh-arithmetic-transfers.zip` | Prime intervals/progressions and Pomerance divisibility applications; prime-plus-cube classification; A4/A5 even-degree isogeny tests and a simultaneous local witness; a one-sided remaining Dedekind-zeta criterion; quantitative fixed-congruence obstruction. | Some long finite arithmetic searches are inputs with supplied certificates. The 66 surviving primes are necessary local possibilities, not existence of curves. Nonabelian estimate is unproved. |
| 02 | `grh-exponent-six-and-transfers.zip` | Completeness of 432 fundamental discriminants of class-group exponent six, and 1,236 order discriminants; prime-gap graph conjectures; local quintic reflection and simultaneous splitting. | Uses an external exhaustive census through 3.1e20 plus the residual-interval exclusion. This turn read the proof and all three checker sources and replayed the rational explicit-formula certificate and both complete paired-norm implementations: 9,393,302 candidates, zero survivors. This supersedes the partial exponent-six reports. The initial external census was not recomputed. |
| 03 | `grh-lean-transfers.zip` | CM/trinomial, genus/class-group, cubic/quintic reflection and prime-race deductions; explicit mechanism overview. | Mainly exported-theorem applications plus analytic reductions. Needs reading in conjunction with later CM/exponent-six completions rather than treating each old residual list as current. |
| 04 | `grh-transfer.zip` | 229 abelian extensions satisfying a sufficient zero-sum condition for prime-ideal Mertens errors; norm-Euclidean quintic/septic transfers; distinct-positive-coordinate xy+yz+zx representations; Kummer irreducible-prime criterion; exact limiting smoothed split-prime error. | New Kummer prime inequality remains open. Finite field census has its own interval certificates and published inputs. |
| 05 | `grh_a6_transfer_2026-11-25.zip` | A6 degree-90 and degree-45 entire monomial detectors; degree-90 subfield detector; local multiplicity inequalities; optimality under stated detector constraints; integer dyadic one-sided equivalences. | Does not prove the required class-sensitive prime bound, nonabelian RH, or general Artin holomorphy. |
| 06 | `grh_beyond_dirichlet_grh_2026-11-25.zip` | Common torsion nonvanishing for integral formal series with total witness budget B at depth h*(r)+floor(B), independent of variable count and degree; simultaneous powers variant; valuation approximation for series, determinant and Fitting ideals; exact odd cocycle/direct-limit locally trivial H1 comparison. | No named major conjecture solved. The cohomology comparison explicitly assumes odd coefficient prime and positive Tate exponent, and retains the source coefficient-ring roots-of-unity hypothesis. |
| 07 | `grh_cm_four_terms_and_prime_bias.zip` | Four-term CM classification; unconditional Riffaut reductions; 28/29 quintic cases; support growth; Suzuki sign questions, Q=138/139 transition and >99.677% density; simultaneous convex balance in multiplicative windows. | Later report 20 closes remaining quintic/global five-term question. General central-zero-related sign criterion is a criterion, not Chowla nonvanishing. |
| 08 | `grh_cm_prime_applications.zip` | Initial CM support growth and 79 residual four-term cases; a 7,959-term certificate; least prime-generating constants down to exponent 2.01; prime plus cube/fourth-power exceptions; sparse twist/scale zero criterion. | Contains fourth-power sampling with reciprocal convexity, explicitly crediting Setiawan prior art. Later CM reports supersede the residual cases. |
| 09 | `grh_cm_sparse_equations.zip` | Four-term classification; five-term reduction to -87,-131,-348,-432,-675 with width checks through 65,536; s(Delta) >> h/(log abs(Delta))^2 under Dirichlet GRH and logarithmic growth exponent 1/2; unconditional lower exponent; exact/inexact near-degree families. | Five residual all-width cases are completed by report 20. The local sparse-polynomial determinant mechanism is genuinely different from applying RH alone, but not a direct instance of the unitary theta-lift theorem. |
| 10 | `grh_cyclic_generator_transfer_2026-11-25.zip` | General cyclic-generator refinement of commutator-Sylow detectors, quantitative multiplicity bound, explicit S8 weights; Gamma-moment [t,Ct] averaging, simultaneous convexification and exponentially large coefficients. | New arithmetic covolume bound remains open; analytic and group refinements already present. |
| 11 | `grh_deficit_transfer_2026-11-25.zip` | Optimal nonnegative Frobenius deficits modulo abelian class functions; constant-removing fixed differences; averaged positive-part criterion; S4 support optimality; Kummer and modular/symmetric-power criteria. | All new RH conclusions are conditional on explicitly missing prime inequalities. Do not mistake the normalized-form application for a new automorphic RH theorem. |
| 12 | `grh_kummer_window_transfer_2026-11-25.zip` | Linear auxiliary window, convexified multiple tests; fixed-log-window positive-block criterion for prime-index Kummer fields; Artin–Hooley density reduction for primitive root 2 using prime-index RH. | Arithmetic-geometric inequality unproved. Explicitly records earlier fourth-power sampling overlap. |
| 13 | `grh_lean_transfer_analysis.zip` | Detailed source audit and scope; two abstract transfers (covolume/rank and sparse auxiliary-prime families); conductor-23 class-character/Hecke target with principal-ideal selector. | New arithmetic and twist-selection inputs missing. Audit is not a local Lean replay. |
| 14 | `grh_method_transfers_2026-11-25 (2).zip` | Positive-part Mellin integrability; dyadic L1/L2 sufficient conditions; signed moving-box criterion with zero-free multiplier and counterexamples; rank/index/denominator loss criterion; K-theory Bernoulli-unit prefilter for degrees 124/128, rank counts, small Hecke reconstruction. | New nonabelian mean estimate and strict-Selmer-to-Hecke bridge/large determinants are unproved. K-theory screening is not a K-group vanishing theorem. |
| 15 | `grh_method_transfers_2026-11-25(1).zip` | Torsion selector for arbitrary bounded integral power-series families with finite total valuation budget and a finite degree-independent grid; positive-excess control; A5 detector; periodic Frobenius obstruction; partial genus-field exponent-six exclusions. | Infinite family extension already exists. A5 prime estimate open. Partial class-group census superseded by report 02. |
| 16 | `grh_method_transfers_2026-11-25.zip` | General periodic Frobenius approximation obstruction; exact reciprocal-variable convex interpolation; nonuniform sampling; fourth-power checkpoints and sharpness; constant-free finite differences; root-count criterion for every number field; ramification-budget obstruction and bounded-support extraction. | The entire proposed fourth-power/Jensen/new positive hinge example duplicates this report. It credits Setiawan for the fourth-power scale and logarithmic-mean literature for the exact loss. |
| 17 | `grh_quantitative_twists_2026-11-25.zip` | Degree-independent polynomial order-exponent bound for a fixed finite packet, positive fraction on an admissible shell, multivariate and bounded-series extensions, determinant/minor applications, common tame-conductor packets. | Bound compares with fixed witness-radius Gauss valuation, weaker than source comparison at the selected shell radius. It does not improve every part of the original theorem. Fixed-order arithmetic nonvanishing and conductor density remain open. |
| 18 | `grh_reflection_transfer_2026-11-25.zip` | For Sn, ord(zeta_L) <= 2(n-H_n) ord(zeta_{L^{<(12)>}}) off-line under Dirichlet GRH; two-class prime criterion; real reflection-group extensions. | No arithmetic prime bound supplied, no nonabelian RH solved. |
| 19 | `grh_relative_prime_races_2026-11-25.zip` | Positive entire relative Dedekind factors in normal towers; cancellation of intermediate strata; constant-free prime-only integer-scale test; S4 weights 8 and -1 on 1^4 and 1·3; mixed-factor composita. | New analytic inequality remains an explicitly open target. |
| 20 | `grh_sparse_singular_moduli.zip` | Claims complete global s<=5 iff h<=4 (unrestricted polynomial exponents), s=h+1 through h=5 except j=0; all five earlier residual cases eliminated; s >> h/log^2 abs(Delta); exact infinite family and >61.33% prime-conductor density; optimal D4 Frobenius criterion. | Six-term threshold for h>=6, linear-in-h universal lower bound and true exact-family density remain open. The D4 analytic inequality also remains open. |
| 21 | `grh_sylow_transfer_2026-11-25.zip` | General commutator-Sylow signed prime statistic equivalent to Dedekind RH given Dirichlet GRH; quantitative Heilbronn character control; PSL2(7) weights 21 and -1. | No general Artin holomorphy assumed; arithmetic estimate missing. Later cyclic-generator refinement in report 10. |
| 22 | `grh_transfer_analysis.zip` | Source audit; standard consequences including least quadratic nonresidue; abstract determinant and analytic extraction; conductor-23 class-character target; seven separately compiled elementary Lean lemmas. | The small Lean verification does not certify target arithmetic inputs or upstream GRH replay. |
| 23 | `grh_transfer_analysis_2026-11-25.zip` | General audit; known consequences (Newman constant, Euclidean classifications); one-sided transform criterion; sufficiently populous auxiliary-prime subfamily; S3 tensor-square target; ramification and witness-quantifier obstructions. | New arithmetic/twist estimate missing. Uncompiled Lean wrappers explicitly marked uncompiled. |
| 24 | `grh_transfers.zip` | Partial exponent-six completeness (429/432 under two conditions); all-scale modulo-four smoothed positive race; cubic -23 eventual-sign equivalence; positive Mellin kernel. | Class-group partial result superseded by 02. Cubic sign is still open. |
| 25 | `psl2_grh_transfer.zip` | PSL2(2^r) optimal pointwise-nonnegative genuine detector of dimension q^2; sharp single/two-subfield degree thresholds; exact prime-root-count one-sided equivalence. | New prime inequality not proved; finite group checks support the stated group claims only. |

## Exact duplicate check: reciprocal convexity and fourth powers

The candidate suggested during this turn is already present, with more detail, in archive 16:

`grh_method_transfers_2026-11-25/report/sparse_sampling.tex`:

- Lines 24–73: exact interpolation with t=1/x, convex H(t), and logarithmic Jensen gap; maximum loss J(r) where r is endpoint ratio.
- Lines 75–107: nonuniform sampling theorem with relative gap O(x^{-theta/2}).
- Lines 109–147: fourth powers for theta=1/2, explicit constants and sharp limsup cost 2A.
- Lines 149–197: discrete positive ramp masses, R(j^r)=0 and positive between-node excess of asymptotic size Ar^2/(8j^2), showing sharpness in the broad positive-measure class.
- Lines 199–235: cancellation of unknown constants by multiplicative finite differences and one-sided telescoping.
- Lines 271–358: equivalence to Dedekind RH for root-count statistics of arbitrary monic irreducible integer polynomials, no global Artin holomorphy assumption.

Archive 08, `grh_cm_prime_applications/audit.tex`, also contains the reciprocal-variable convexity proof, fourth-power sampling and sparse auxiliary twist selection. It explicitly credits Sandi Setiawan for the prior fourth-power mesh and chord argument. Archive 12 explicitly acknowledges all this prior work. The new report should not claim this candidate as a fresh theorem.

## Exact duplicate check: means and robust averaging

Archive 14, `sections/mean_transfer.tex` and `sections/mean_additions.tex`, already proves weighted positive-part Mellin convergence criteria; dyadic positive-part L1 and L2 sufficient estimates; signed moving-box integration with multiplier (h^s-1)/s; weighted boxes with multiplier (h^{s+nu}-1)/(s+nu); counterexamples to sparse signed sampling and arbitrary positive smoothing; and rank-sensitive combined-loss control. Thus merely replacing pointwise estimates by averages is also not new relative to the supplied corpus.

## Concrete genuinely unfilled interfaces

### 1. Arithmetic, rather than detection, for the conductor-23 cubic

Let H be the splitting field of X^3-X-1, K=Q(sqrt(-23)), and psi a nontrivial class character of K. Existing reports establish the factorization zeta_H=zeta·L(chi_-23)·L_K(psi)^2 and formulate multiple exact criteria. A useful next result must produce real information about the principal-ideal selector or its arithmetic lattice, not another equivalent restatement of its zeros.

One existing target is integral_X^{2X} (R_H(x)_+)^2 dx <<_epsilon X^epsilon with R_H normalized as in archive 14, sections/mean_additions.tex. Source second moments average forms/translates; this target averages the prime scale. Identifying these variables without a comparison theorem would be invalid. No inspected report supplies that bridge.

### 2. Strict Selmer and K-theory

Archive 14 identifies possible next degrees 124 and 128 and computes Bernoulli-unit and rank data. What remains is a precisely quantified ordinary strict-Selmer-to-Hecke witness theorem, correct Frobenius normalization at probes, coverage of all admissible branches, and exact determinant certificates. Multiple pointwise existential witnesses cannot be silently replaced by one common eigenform. A new determinant alone is insufficient unless its cohomological meaning is proved.

### 3. Torsion selection: quantitative questions still listed as open

Archive 17 has n finite constraints, c=1-1/p, C=1+max_i(B_i+delta_i), P=product_i(1+c B_i/delta_i), and the sufficient bound H=ceil((h0+C)P^{1/(c eta)}). It yields more than fraction 1-eta good primitive roots on some shell h0<=h<=H, relative to a fixed-radius Gauss budget. Its explicit open questions are improving the exponent n/(c eta); polynomial dependence independent of packet size while preserving total positive excess; translating shell density to conductor-norm density; or supplying a concrete arithmetic interpolation system with witnesses and Euler-factor control. None is settled by the finite packet selector alone.

### 4. Odd cocycle comparison exclusions

Archive 06, `sections/odd_sha.tex`, proves the comparison only for odd ell and e>0. It uses division by two to obtain a unique odd cocycle representative; at ell=2 the representative map has a possible 2-torsion kernel and cokernel. At e=0 the local scalar used for local H1 vanishing is zero. Extending these cases needs explicit correction terms; pretending the old proof already covers them would be false. This is a short plausible further lemma, but not automatically a new large-conjecture result.

### 5. CM support threshold after the latest completion

The next genuine question in archive 20 is whether every singular modulus of degree h>=6 needs at least seven nonzero terms. The five-term residual list is no longer an unfilled target in the supplied corpus. The report also asks for s(Delta)>=c h(Delta) universally and the exact density of prime-conductor orders with s=h+1. These could be meaningful arithmetic advances, but they require new local/global input beyond quoting the theta-lift architecture.

## Recommended way to use this audit

Use the corpus as a baseline of already-written deductions and an explicit map of unresolved interfaces. A credible new contribution can be a separately proved strengthening of one interface, a correction of a false extrapolation, a verified formal implementation, or a genuinely new arithmetic case. Do not attach the source's Lean verification to uncompiled downstream statements. Do not call a numerical absence-of-counterexamples test a proof of the infinite prime inequality. Do not claim worldwide novelty based on this finite corpus review.


## Validation addendum after the first inventory

### Exponent-six census independently replayed

The full note is `prior/exponent_six/VALIDATION.md`. After inspecting all code, both supplied complete finite implementations were replayed successfully: 414 eligible primes, 85,491 pairs, 9,393,302 candidates above 3.1e20, zero survivors. The exact rational explicit-formula test passed as well. The mathematical norm-collision and residue-witness reduction was checked directly. Published EKN Table 1 and Table 2 and Aiken et al. Theorem 1.3(5) were opened and checked. Thus this particular prior completion is now more than an inventoried claim: its extra residual-interval proof has been reviewed and its full finite certificate independently rerun, conditional only on its explicitly stated external inputs (quadratic GRH and the published initial census).

The 432-field CSV was checked for uniqueness, exponent labels and maximum discriminant 5,761,140. The reviewed table-check program verifies 1,236 distinct order discriminants, maximum 43,522,752, the published author-table Git blob hash, and exact agreement of its 432 maximal orders with that field list. These count/matching checks are separate from verifying all order-class arithmetic, which was not rerun.

### CM certificate inputs checked independently

An independently written standard-library script, `code/check_selected_cm_inputs.py`, verifies all 18 Newton-disk certificates in archive 20's residual list, all 245 stated reduced forms, and all 17 confluent-period identities used for the final quintic and four sextics. It does not import or execute old archive code. All exact checks passed. I checked the local sparse-root, global split/nonsplit and divided-difference reductions on paper and found no gap. The large residue sieves and class-polynomial identifications were not independently replayed, so the full CM classification retains that evidence boundary.

### Nonduplication of this turn's newer candidate lemmas

A complete search of the extracted TeX/Markdown corpus, followed by reading the relevant averaging and sparse-sampling sections, found no theorem converting positive-ramp Lp positive-part means into pointwise bounds via semiconvexity, and no joint finite-family positive-kernel criterion based on absence of common Mellin zeros. The older mean report treats one zero-free moving-box multiplier, and explicitly supplies a positive two-tap kernel that hides poles; it does not give the proposed two-incommensurable-kernel repair. This establishes nonduplication within the inspected corpus only, not worldwide priority.
