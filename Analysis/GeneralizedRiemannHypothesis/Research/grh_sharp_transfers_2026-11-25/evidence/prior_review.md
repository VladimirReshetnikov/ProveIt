# Prior-report review and comparison

## Provenance and review scope

The GitHub plugin resolved ProveIt main to commit
274841c1cb137aafbb60ab5f519c51fd42eee98e (2026-11-26 05:36:52 UTC;
2026-11-25 Pacific date). The incoming directory contains 31 ZIP archives
and its unrelated cumulative intake README.

All 31 archives were retrieved, extracted, checked for exact byte length,
and verified against their Git blob SHA-1 identifiers. Full retrieval is
recorded in verified_corpus.json; incoming_manifest.json preserves the
directory metadata and pinned raw source URLs. Targeted manuscript sections
and abstracts were read. Retrieval and comparison do not independently
certify every theorem or replay all prior finite calculations.

## Main comparison relevant to the present contribution

| Archive | Material actually examined | Established or claimed prior content | Relation to the present work |
| --- | --- | --- | --- |
| grh_exact_torsion_transfer_2026-11-25.zip | Full sections/exact_torsion.tex; corpus, references and abstract | Exact fixed-radius aggregate specialization with H0=h0+ceil(p^h0 B(h0+B+2)), arbitrary finite dimension and bounded series; exact individual and moving-baseline counterexamples | Present proof replaces this sufficient quadratic bound by the sharp H=h0+floor(B p^(h0-1)) and determines the exact obstruction budget |
| grh-torsion-and-zero-data.zip | Full torsion.tex, minimax.tex; phase discussion | Exact shell extremum U_h(m); exact total-positive-loss obstruction cost; exponential tolerance lower bounds; bounded-ramification improvement | Supplies an antecedent for the one-shell combinatorics. It optimizes positive individual loss or moving Gauss baseline, not fixed aggregate loss |
| grh-torsion-and-prime-sampling.zip | Full sections/torsion.tex; field, cyclotomic and limits sections | Exact positive-part minimax for general starting depth; C_(p,delta)=sum m_h/e_h; C~delta log H; fixed-field refinements | Distinct global extremal problem. Its field.tex leaves fixed packet-cardinality optimization as a further question |
| grh_quantitative_twists_2026-11-25.zip | Abstract and quantitative selector sections | Positive tolerances for fixed finite packets; polynomial order-exponent dependence with packet-dependent exponent; positive fraction of good primitive roots | Present exact aggregate result does not replace its separate individual tolerances or density conclusions |
| grh_method_transfers_2026-11-25(1).zip | Torsion sections, full a5_transfer.tex, abstract | Bounded power-series families; explicit A5 positive detector; genus-family exclusions | Earlier qualitative/countability interfaces remain useful; fixed abelian data obstruction is already present |
| grh_beyond_dirichlet_grh_2026-11-25.zip | Full series_fitting.tex and overview | Uniform truncation/algebraic approximation extends source polynomial selector to bounded series; simultaneous Fitting profiles, odd-cohomology comparison | Determinantal application must preserve aggregate-versus-individual distinction; presentations and witness minors are additional arithmetic inputs |
| grh_method_transfers_2026-11-25 (2).zip | Full mean_transfer.tex, mean_additions.tex | Positive-part Mellin criterion; dyadic L1/L2; averaged determinant losses; Holder inverse-rank moments; moving signed windows; counterexamples | Do not repackage exceptional-height or Lp averaging as new here |
| grh_deficit_transfer_2026-11-25.zip | Full analytic and group-detector sections | Constant-free multiplicative difference, averaged positive-part detector, optimal nonnegative lifts modulo abelian class functions, S4/Kummer/modular targets | Existing analytic reductions; missing arithmetic estimate remains |
| grh_relative_prime_races_2026-11-25.zip | Main theorem and comparison sections | Relative-zeta positive combinations, normal-tower cancellation, S4 weights 8,-1, composita, off-line Artin zero/pole consequence | Existing avoidance of individual Artin holomorphy; no prime inequality proved |
| grh_sylow_transfer_2026-11-25.zip | Abstract, Heilbronn and multiplicity sections | Universal Sylow-induced entire-Hecke detector; PSL2(7) example; quantitative local-order inequalities | General Heilbronn detector approach is already developed |
| grh_cyclic_generator_transfer_2026-11-25.zip | Abstract, Heilbronn/interface and window sections | Universal cyclic-generator refinement of Sylow detectors; S8 example; linear logarithmic auxiliary windows | The tensor detector is distinct only in its representation construction and explicit identity-domination argument |
| grh_reflection_transfer_2026-11-25.zip | Abstract and multiplicity theorem | Reflection detector; Sn transposition test and ord(zeta_L)<=2(n-H_n)ord(zeta_E) | Further prior sparse-detector family |
| grh_a6_transfer_2026-11-25.zip | Abstract, exact identities and Artin-order section | A6 degrees90/45 monomial and degree90 permutation detectors, sharp scoped optimization, one-sided criteria | Nonabelian criterion, no new unconditional RH |
| psl2_grh_transfer.zip | Abstract and detector/Artin sections | PSL2(2^r) nonnegative character of dimension q^2, sharp subfield degrees, root-count criterion | Distinct prior family; uses Heilbronn cyclic restrictions |
| grh_kummer_window_transfer_2026-11-25.zip | Abstract and target sections | Fixed-log-window Kummer criterion; conditional Artin–Hooley density reduction; linear log-window argument | Artin primitive-root conjecture still depends on a new prime estimate |
| grh_structural_transfers_2026-11-25.zip | Full duality.tex, abstract and hypothesis discussion | Rational conjugate Tate-duality forces infinite congruenceTerm; anticyclotomic twists preserve it; exact Smith-length correction; surviving BSD polarization obstruction | A sharp torsion selector cannot remove this missing structural hypothesis |
| grh_transfer_analysis.zip | Main source/mechanism, analytic and cubic-target sections | Original source audit, common-covolume cancellation, cubic principal-class target and missing arithmetic estimate | Foundational benchmark already present |
| grh_transfer_analysis_2026-11-25.zip | Abstract and source scope | General one-sided criterion, sparse auxiliary-prime families, cubic tensor-square target | Foundational analytic comparison |
| grh_lean_transfer_analysis.zip | Manuscript source map and selected sections | Source architecture, rank/covolume and cubic transfer lemmas | Foundational comparison |
| grh_method_transfers_2026-11-25.zip | Main report and headings of periodic_obstruction, ramification_budget, sparse_sampling | Fixed periodic obstructions, ramification budgets and sparse sampling | Prior local/interface results |

## Additional arithmetic report families

The remaining eleven archives were inventoried and their overview or principal
claims read. Their claims were not used as assumptions in the sharp torsion proof
and their full computations were not replayed.

- grh-arithmetic-transfers.zip: arithmetic progressions, CM/isogeny restrictions,
  and further nonabelian detector calculations.
- grh-exponent-six-and-transfers.zip: imaginary-quadratic exponent-six census
  and transfer refinements.
- grh-lean-transfers.zip: CM/genus/class-three and quintic material.
- grh-transfer.zip: claimed 229-field abelian Mertens-error classification,
  norm-Euclidean consequences, prime representations and Kummer criteria.
- grh_cm_four_terms_and_prime_bias.zip: claimed four-term singular-modulus
  exclusion, residual-case closure, Suzuki prime-error questions and balance.
- grh_cm_prime_applications.zip: sparse singular-modulus relations, prime-generating
  constants, prime plus prime-power classifications and thin sampling.
- grh_cm_sparse_equations.zip: sparse CM relation refinements and four-term closure.
- grh_sparse_singular_moduli.zip: sparse CM relations, finite sieves and Frobenius
  constraints.
- grh_transfers.zip: exponent-six classification and prime-race/cubic criteria.
- grh_transfers_singular_moduli_and_symmetric_powers.zip: singular-modulus and
  symmetric-power weights.
- dirichlet-grh-research.zip: heavenly elliptic/abelian varieties and O'Hara
  finiteness questions, shifted critical-line Euler products and periodic
  geometric progressions.

## Verdict on overlap and novelty language

No retrieved predecessor states the fixed-aggregate exact obstruction budget
(H-h0+1)p^(1-h0), nor the sharp endpoint h0+floor(B p^(h0-1)).
The predecessor with exactly the same aggregate objective explicitly states
that its quadratic endpoint is deliberately conservative and not optimal.
The newest exact minimax manuscripts use a different objective, under which
early-shell savings are discarded through a positive-part operation.

Accordingly it is justified to call the new result an exact improvement of
the inspected research program. Worldwide priority still requires a dedicated
literature review; the cyclotomic shell argument belongs to the established
background of p-adic fixed divisors, P-orderings and maximum-modulus principles.
The result is a local specialization theorem, not a solution of a named major
arithmetic conjecture.

