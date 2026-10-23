# Research status

Updated 23 October 2026. This is a work log, not a completion certificate.

The historical manuscript collection has moved from the Cardinals reports
tree to [con-zfc-diophantine-forms](con-zfc-diophantine-forms/README.md),
at the repository owner's request. Live catalogue/intake/research links
were updated. Pinned historical source paths remain valid for their named
commits and are deliberately retained in the delivered provenance records.

| Component | Status | Evidence / next task |
|---|---|---|
| Reports and historical comparison | Initial audit complete | Wave-5 collection README; P67 circuit in package 36 |
| Wave-6 reports | Merged; comparison started | Packages 38–45 placed by `124c07c0b7`, merged at `2d7766807b`; direct quadratic coding is a further size-reduction route |
| Wave-7 proposals and target review | Historical target retained as checkpoint | Packages 46–53 at `6d375f2d2d`, merged at `d869b0ddbf`; selected package 52's nine-positive 548-operation form at that stage; see `PROPOSAL_REVIEW.md` |
| Wave-8 proposals and proof checkpoint | Reviewed; checkpoint preserved | Packages 54–59 at `beb0192cb8`; all six full finite replays PASS; package 59 adjunct has nine positive variables, 473 operations, degree 1,910,404; see `PROPOSAL_REVIEW_WAVE8.md` |
| Wave-9 proposals and next numerical targets | Reviewed | Packages 60–67 at `a2cd79b912`; all eight full normal release replays PASS; delivered nine-positive cost target 66:444/1,845,940; separate compact54-sharp instance passes sealed replays at 443 positive / 450 natural operations, same degree; see `PROPOSAL_REVIEW_WAVE9.md` |
| Compact split-form coefficient instances | Generated and independently replayed | Whole package-54 / package-57 tuples, same 473 operations and degree 1,910,404; preferred sharp native payload 215,492 raw bytes and live derived constants 1,672,725 bytes; see `candidates/split116-compact/README.md` |
| Split-form generic source contract | Lean checked | Full binomial-to-bounded-source-coefficients equivalence, derived degree/quarter bounds, unconditional word positivity and exact outer ratio; native calibration remains separate; see `SPLIT116_FORMALIZATION.md` |
| Literal split116 source and unbounded nine-coordinate equivalence | Lean checked | `SplitNineSource59.exists_natural_zero_iff_source_compact54`: exact authoritative old-z source, all 89 kernel records, four explicit port boxes; no supplied height, degree, packing or population premise; see `SPLIT_SOURCE59.md` |
| Literal split116 nine-variable polynomial | Lean checked | `SplitNinePolynomial59`: actual `MvPolynomial (Fin 9) Int`, ring-map and natural evaluation identities, source-zero iff; literal480 natural DAG identified with recipe in `SplitCircuitRecipe59` |
| Shared split116 base powers | Lean checked | Exact generic-ring and MvPolynomial rewrite at456/463 positive/natural operations, full liveness/counts; both polynomials identified with source recipe including all12 fixed-leaf expressions; positive/natural root equivalence checked; see `SPLIT_POSITIVE_RECIPE59.md` |
| H2082 affine positive source change | Lean checked | `GapSource66.positiveZeroEquiv` and `exists_positive_nat_zero_iff` preserve the full positive zero set by explicit inverse maps, using only literal source rows and beta positivity; no Pell or native calibration premise; see `GAP_SOURCE66.md` |
| H2082 literal extraction and kernels | Lean checked | `GapGeometry66`, `GapCertificate66`, `GapKernelData66`, `GapKernels66`: all85 records and22450 degree-matched interactions, exact source-zero extraction, sharp four-port height and degree≤2082; see `GAP_KERNELS66.md` |
| Compact H2082 ratio calibration | Lean checked | `GapNineRatio66`: block exponent2200, threshold `2^(15*a+79)*B^1162`, half-height a; exact population calibration including b=1, derived finalizer bounds and sound/complete ratio; see `GAP_NINE_RATIO66.md` |
| H2082 unbounded nine-coordinate source equation | Lean checked arithmetic endpoint | `GapNineSource66.exists_natural_zero_iff_source_compact54`: all source bounds/carry/ranges derived, explicit cofinal witnesses, half-height432007 and four port boxes; `compact54_zero_iff_split59` compares old/new unbounded zero existence under beta positivity; native calibration remains separate; see `GAP_SOURCE_NINE66.md` |
| H2082 actual nine-variable polynomial | Lean checked | `GapNinePolynomial66`: actual `MvPolynomial (Fin 9) Int`, every85 coefficient record, generic scalar/map identities, natural evaluation/source equivalence and old-polynomial zero equivalence; native calibration remains separate; see `GAP_NINE_POLYNOMIAL66.md` |
| H2082 counted positive/natural circuits | Lean checked | `GapCircuitRecipe66`, `GapCircuitTranslation66`, `GapPositiveRecipe66`: actual443/450 DAGs identified with scalar and MVP source recipes, all11 fixed leaves bound coherently, complete positive/natural root correspondence; see `GAP_CIRCUIT_RECIPE66.md` |
| H2082 cancellation-aware degree | Lean checked upper bound | `GapPolynomialDegree66`: actual443/450 polynomials and source recipes have degree≤1,845,940; checked484 local labels plus Pell-defect and recentering cancellations; exact-degree lower bound remains a finite-audit result; see `GAP_DEGREE66.md` |
| Signed native Pell step-down | Lean checked | `NativePellStepDown`: signed minus-form index recovery and safe strong-quotient restoration; recovered main sequence and bootstrap hypotheses remain explicit; see `NATIVE_PELL_STEP_DOWN.md` |
| Literal native Pell bootstrap and index | Lean checked | `NativePellBootstrap.source_main_index_exact`: main classification, native window bounds, strong bootstrap and exact native index from literal old-z source and native port relations; payload/compiler calibration remains separate |
| Native first index and binary scale | Lean checked arithmetic prerequisites | `NativePellFirstIndex`, `NativePellPower`, `NativeBinaryScale`, `NativePellScaleBounds`: exact odd first index, actual source `X=2^R`, `q=(2^d)^N` and cubic common scale; subsequent half-binomial and arithmetic-window extraction checked; whole fixed-payload/compiler calibration remains open; see `NATIVE_PELL_POWER.md` |
| Literal source to native arithmetic window | Lean checked forward bridge | `NativeHalfBinomial`, `NativePopulationLower`, `NativeMaskPopulation`, `NativeSourceMask`, `NativeSourceWindow`: doubled ratio, exact saturation/mask tests, radix/repunit, spatial power and old-z transport derived from actual source under explicit coefficient interface; whole-tuple Wang/K215 binding and converse completeness remain open; see `NATIVE_SOURCE_WINDOW.md` |
| Compact54 native local clause decoder | Lean checked | `NativeSelectorClause54.native_clause_iff`: arbitrary Boolean457-selector assignments force exactly empty or one allowed tile, complemented copied labels and synchronized anchors; actual coefficient recipes and pinned literal modes checked; global convolution/phase/compiler bridge remains open; see [NATIVE_CLAUSE54.md](NATIVE_CLAUSE54.md) |
| Exact meaning of consistency | Identified | `¬ BProv ZFCax_s [] Form.fBot`; existing unconditional K215 endpoint |
| Concrete recursively enumerable refutation predicate | Lean checked | `Computability.refutationInputs_re` and `Bridge.zfcRefutationInputs_re`; actual six-register enumerator |
| Direct sealed-ZFC proof checker | Lean checked | `AnnotatedProofChecker.exists_refutation_iff`: executable parent-index certificates with explicit axiom/schema tags, exactly the original17 rules; no K215/Jones dependency, no choice in data or audited proof |
| Direct checker numeric encoding | Lean checked | `AnnotatedProofCode.exists_checked_code_iff`: total fuel parser, typed roundtrips, unique decoded quote, truncation rejection, and exact numeric refutation existence; complete PR/graph compilation and internal-code transport remain open |
| Direct checker local PR arithmetic | Lean checked | `AnnotatedCodeArithmetic`: literal ScalarPRCode data for tree constructors/projections, guarded list lookup and exact context+formula reference checking; full checker compilation remains open |
| Direct checker renaming certificates | Lean checked | `AnnotatedRename` and `AnnotatedRenameCode`: finite numeric tables for actual shift/instantiation under arbitrary binder depth, exact soundness/completeness, guarded references; whole-table PR program now checked in `AnnotatedRenameScanPR`, 3605 nodes / 3329 after certified optimization; internal model-omega interpretation remains open; see `ANNOTATED_RENAME_VALIDATOR.md` |
| Direct checker additive bound and sealing certificates | Lean checked external arithmetic | `AnnotatedBoundScan.exists_seal_program_iff`: exact numeric certificates for actual `bound` and `sealF`; whole sealing PR program2279 nodes /1983 optimized; axiom dispatch, proof-line validation and internal coding remain open; see [ANNOTATED_BOUND_SEAL.md](ANNOTATED_BOUND_SEAL.md) |
| Direct checker actual schema programs | Lean checked external arithmetic | `AnnotatedSchemaMaps`, `AnnotatedSchema`, `AnnotatedReplacement`: all four actual variable maps, literal body assembly, raw-input schema validation and sealing; exact existential languages for actual sealed Separation/Replacement axioms,10241/25535 program nodes; axiom dispatcher, full proof-line validator and internal code transport remain open; see [ANNOTATED_SCHEMAS.md](ANNOTATED_SCHEMAS.md) |
| Nine-variable specialization | Lean checked | `zfcNinePolynomial_noZero_iff_conZFC`, no premises; existence-based coefficients |
| Quartic alternative | Lean checked | `zfcQuarticPolynomial_noZero_iff_conZFC` and total degree at most four |
| Direct executable quartic without Jones compression | Lean checked external endpoint | `DirectQuarticZFC.noNaturalZero_iff_conZFC`, actual syntax/polynomial evaluation identity and degree at most four; `QuarticCost` proves at most `6*(nu+1)` tree operations; numerical `nu` remains unmeasured; see `ALTERNATIVE_ENCODINGS.md` |
| Closed direct-quartic size bound | Lean checked conservative bound | `DirectQuarticSize.variableCount_lt`: actual compacted natural-variable count `<2^300000`, from source witness count plus one≤`2^22426`, depth≤140000 and exact bounded-iteration metadata; exact count remains unmeasured; see `NATIVE_QUARTIC_SIZE.md` |
| Shared arithmetic DAG to quartic | Lean checked compiler | `DAGQuartic.exists_polynomial_zero_iff`: arbitrary signed intermediates, `n+2*m` natural slots, degree≤4, at most `12*m+4` tree operations; complete proof checker compilation remains open; see `DAG_QUARTIC.md` |
| Nonnegative arithmetic DAG to quartic | Lean checked compiler | `NaturalDAGQuartic.exists_polynomial_zero_iff`: two-output equality, nonnegative constants and addition/multiplication, `n+m` natural slots, degree≤4 and at most `6*m+4` tree operations; whole-checker compilation remains open |
| Supplied shared natural-register builder | Lean checked | `NaturalRegisterProgram`: literal/input/add/mul constructors append one register, old values and sharing preserved; output equality gives actual `Rep` with exactly m gate witnesses, degree≤4, operations≤6m+4; concrete shared-square regression checked; whole checker compilation remains open; see `NATURAL_REGISTER_PROGRAM.md` |
| Shared-register existential scopes and pairing graphs | Lean checked | `NaturalRegisterRelation` compiles explicit auxiliary inputs with exactly k+m witnesses; `RegisterNatPairing` covers the direct checker's actual max-square `Nat.pair/unpair` (41 witnesses, degree≤4, ≤238 operations per projection), `RegisterCantorPairing` separately covers the older enumerator (11 witnesses, ≤64 operations); whole checker compilation remains open; see [SHARED_REGISTER_RELATIONS.md](SHARED_REGISTER_RELATIONS.md) |
| Quadratic constraints on shared registers | Lean checked compiler and local reductions | `QuadraticRegisterSystem` adds no gate witnesses for supplied quadratic rows; exact max-square pairing3 witnesses, each unpair projection4/46 operations, guarded joint div/mod1/16, all degree≤4; complete checker composition and internal interpretation remain open; see [QUADRATIC_REGISTER_SYSTEM.md](QUADRATIC_REGISTER_SYSTEM.md) |
| Explicit, computable coefficient recipe for ZFC | Lean checked | `ExplicitZFC.expression` is a closed executable definition; numerical payload not materialized |
| P67 compiler correctness in Lean | Open | The report's ordinary proof is not yet a Lean proof |
| Object-level ZFC derivation | Open | External equivalence and internal provability are separate claims |
| Global simplicity minimum | Not claimed | No common ordering of all size measures; no optimality theorem |
| Short-equation local simplification | Lean checked | `ShortEquation.scaled_zero_iff_reduced`, no compiler hypothesis |
| Literal 69-operation polynomial | Lean checked | `ShortCircuit.eval_polynomial_zero_iff_baselineValue_zero`; scalar and MvPolynomial evaluation both included |
| Literal 75-operation polynomial, degree 68 | Lean checked | `ShortSystem.eval_compactPolynomial_zero_iff_baselineValue_zero` and `compactPolynomial_totalDegree_le` |
| Literal 73-operation polynomial, degree 80 | Lean checked | `ShortFrontier.eval_polynomial_zero_iff_baselineValue_zero` and `polynomial_totalDegree_le` |
| Literal 76-operation polynomial, degree 64 | Lean checked | `ShortReducedStrong.value_zero_iff_compactValue_zero` for all integer assignments; actual polynomial and degree bound checked |
| Consecutive-product negative Pell obstruction | Lean checked | `ConsecutivePell.norm_ne_neg_one` for every integer `n ≥ 2` |
| Executable representation data | Lean checked primitives; integration open | `Representation`, `ArithmeticRepresentation`, `NaturalExpression`; see `COMPILER.md` |
| Explicit arithmetic and bounded quantification | Lean checked | Supplied Pell, power, binomial, factorial and bounded-forall representations; no representation selected from existence proofs |
| Supplied representation to nine-variable equation | Lean checked | `EquationFromRep.construct`: explicit normalized quartic, literal index, expression and polynomial, natural solvability/unsolvability equivalences |
| Executable supplied-data Jones compiler | Lean checked | `ExecutableJones.fromRep`, sparse coefficient reader, explicit coding sums/index; exact evaluation agreement with the mathematical polynomial |
| Primitive-recursive graph compiler | Lean checked | `ScalarPRCode.graphRep`, structural on all seven program constructors, including the full bounded transition trace |
| Concrete refutation-program data | Lean checked | `DirectEnumerator.program : ScalarPRCode.Realizes haltingTest`, constructed directly from arithmetic source semantics |
| Closed executable consistency equation | Lean checked | `ExplicitZFC.noSyntaxZero_iff_conZFC` and `noNaturalZero_iff_conZFC`, with no supplied-data hypothesis |
| Closed equation from direct arithmetic graphs | Lean checked | `NativeZFC.noNaturalZero_iff_conZFC`; native Cantor/branch graphs and one outer iteration trace |
| Native formula blocks and direct composition | Lean checked | One-step source graph reduced from 6,924 through 1,811 to 1,742 witnesses; complete quartic/Jones counts remain unmeasured |
| Nine strictly positive integer unknowns | Lean checked | `PositiveZFC.noPolynomialZero_iff_conZFC` and the exact natural-to-positive shift |
| Polynomial-size quadratic positions | Lean checked foundation | `SidonPositions`: explicit cubic-size weights, exact unordered-pair uniqueness; full quadratic/Jones adaptation remains open |
| Quadratic coefficient extraction | Lean checked foundation | `QuadraticCoding`: the complementary encoding extracts twice each supplied quadratic value at a cubic-size position |
| Simultaneous quadratic extraction | Lean checked foundation | `MultiQuadraticCoding`: one combined polynomial recovers every supplied quadratic row, with a bound linear in rows and cubic in source dimension |
| Simultaneous quadratic carry test | Lean checked foundation | `MultiTargetCarry`: exact rowwise zero test by one central-binomial divisibility condition, under explicit coefficient and packing bounds; see `QUADRATIC_CODING.md` |
| Support-sensitive quadratic extraction | Lean checked | `SelectiveQuadraticCoding`: arbitrary weights and row targets; unused pairs may collide and row intervals may overlap |
| Literal selective position certificates | Lean checked | `SelectiveCertificate46` protects 62 pairs; `SelectiveCertificate52` protects 71 and supplies regular-target extraction on that support |
| Literal package-52 quadratic source | Lean checked | `NativeQuadraticParent`: exact 60 gates, 22 rows, 136 coefficient records and equality with the actual positive source; see `SELECTIVE_SOURCE52.md` |
| Package-52 positions and coefficient height | Lean checked | `NativeQuadraticPositions`: exact kernel degree 7,516 and product degree below 7,865; `NativeCoefficientBounds`: corrected coefficients below `2^1182955` under explicit port bounds |
| Sparse low-mask decoding | Lean checked | `LowMaskCoding`: exact arbitrary-position encoding, unused digits zero, actual input weight zero and dummy position 81 covered |
| Selective coefficient and packing bounds | Lean checked | `SelectiveCarry`, `SelectiveCoefficientBounds`, `PolynomialRangeBounds`: full polynomial, half-base, pre-decoding range and two-block central-binomial contracts |
| Package-52 ratio substitution and finalizer | Lean checked | `NativeNineRatio52` and `NativeNineFinalizer52` close the exact arithmetic tail against the existing Jones theorem |
| Assembled package-52 arithmetic source contract | Lean checked | `NativeQuadraticSource52.source_contract` and `NativeNineSource52.natural_zero_iff_source_published`; nine natural coordinates, explicit four-port size bounds |
| Literal package-52 source-equivalent polynomial | Lean checked | `NativeNinePolynomial52`, `NativeNineEquation52.exists_zero_iff_source_published`; actual `MvPolynomial (Fin 9) ℤ`, no truncated arithmetic; native calibration and shared-evaluator count remain separate |
| Native arithmetic source elimination | Lean checked | `NativeArithmetic52`: explicit 31-to-16 coordinate lift and seven residuals, preserving positivity conditions; old transport conventions require their own domain translation |
| Sharp majorant and two-root finalizer | Lean checked | `NearSquareFinalizer.exists_value_zero_iff` gives two square tests, divisibility and positive margin; source packing and native calibration remain separate |
| Ordinary-strong minimum-norm finalizers | Lean checked local theorem | `MinimumNorm.gap_minima75_zero_iff` / `gap_minima76_zero_iff` formalize package 47's local minimum arguments; literal circuit and native rank/calibration bridges remain separate |
| Internal ZFC addition | Lean checked | `ObjectArithmetic.zfc_proves_addition_total` and `zfc_proves_addition_unique` are actual `BProv` derivations; see `OBJECT_ZFC.md` |
| Internal addition laws | Lean checked | `ObjectAdditionLaws` and `ObjectAdditionCancellation`: definable-induction proofs of zero/successor, commutativity, associativity, cancellation and zero-sum criterion on every internal natural; actual closed ZFC derivations of commutativity/associativity/cancellation; see `OBJECT_ADDITION_LAWS.md` |
| Internal multiplication and natural expressions | Lean checked | Actual ZFC totality/functionality proofs in `ObjectMultiplication` and `ObjectNaturalExpression`; `ObjectMultiplicationLaws` and `ObjectDistributivity` prove all-internal-omega zero/successor/commutativity/associativity/distributivity with actual closed ZFC derivations |
| Actual polynomial-side object sentence | Lean checked | `ObjectEquation.unsolvabilitySentence`, exact semantics over all internal natural tuples; the internal consistency iff is still open |
| All-model semiring interpretation | Lean checked | `ObjectOmegaSemiring` packages the entire internal omega as a nontrivial commutative semiring; `ObjectNaturalSemiring` identifies actual expression/equation/no-zero formula semantics with semiring evaluation, including nonstandard tuples; arbitrary external arithmetic transfer is not supplied; see `OBJECT_OMEGA_SEMIRING.md` |
| Internal sum-of-squares compiler step | Lean checked actual ZFC derivation | `ObjectNaturalOrder`, `ObjectNaturalZero`, `ObjectResidualSquares`: internal differences, canonical ordered cancellation, no zero divisors and exact finite residual conjunction; `zfc_proves_residual_conjunction` covers every internal natural tuple; complete representation/consistency equivalence remains open; see `OBJECT_RESIDUAL_SQUARES.md` |
| Internal literal tree-to-quartic compiler | Lean checked actual ZFC derivation | `GatesSemiring`/`QuarticSemiring` identify the actual stored residuals over arbitrary semirings; `ObjectQuarticCompiler.zfc_proves_compiler` proves equivalence of actual source/compiled no-zero sentences over entire internal omega, with actual target degree≤4; full proof-checker representation/internal consistency calibration remains open; see [OBJECT_QUARTIC_COMPILER.md](OBJECT_QUARTIC_COMPILER.md) |
| Unbounded internal consistency sentence | Lean checked for unsealed coding | `ObjectConsistency.unsealedConsistencySentence`; the internal sealed/unsealed proof-certificate bridge remains open |
| Internal universal closure, bounds and sealing | Lean checked | `ObjectCodeClosure`, `ObjectCodeBound`, `ObjectCodeSeal`: nonstandard-input totality, functionality, exact syntax quotation and actual ZFC proofs |
| Sealed internal consistency target | Lean checked sentence and semantics | `ObjectCodeSeal.consistencySentence` quotes actual `ZFCax_s` axioms; equivalence to the internal polynomial remains open |
| Further short-equation reduction | In progress | Current checked frontier: 69 operations/degree 111, 73/80, 75/68, 76/64 |

## Validation environment

During synchronization, `origin/main` added eight wave-6 packages beside
wave 5. The source material remains in the new research directory. Their
entry-point claims include nine-positive degree 129,875,980 / 788 operations
([45](con-zfc-diophantine-forms/45-multioutput/README.md)), ten-integer degree
237,520,456 / 782 operations
([40](con-zfc-diophantine-forms/40-packing10/README.md)), and an eleven-positive
family ([38](con-zfc-diophantine-forms/38-batching11/README.md)). These delivered
mathematical reductions still distinguish their finite checks from a new
end-to-end Lean theorem. Their coefficient tuples are separate bindings;
the current local P67/P69/P73/P75 proofs retain their prescribed package-36
tuple. A smaller generic coding stage can be investigated after the concrete
program-data bridge is closed.

The checkout uses Lean `v4.32.0` and Mathlib `v4.32.0`. A standard Lake build
of the ZFC endpoint and short-equation modules has completed successfully,
reusing matching Mathlib dependencies. The new modules also have independent
axiom checks; completed audits use only `propext`, `Classical.choice`, and
`Quot.sound`.

## Checked local simplification

`Lean/DiophantineConsistency/ShortEquation.lean` compiles under Lean 4.32.0.
`Lean/checks/ShortEquationAxioms.lean` reports only `propext`,
`Classical.choice`, and `Quot.sound` for its main equivalence. The ring
identity uses only `propext` and `Quot.sound`.

The theorem proves cancellation of the nonzero discriminant and reduction
of the auxiliary coefficient. Its crucial premise is proved modulo 4:
`f² - ((a+2)²-1)t² ≠ -1`. An integer product equal to 1 therefore forces
this factor to be +1, which justifies the coefficient replacement in both
directions. This is an equality of complete zero sets, not a comparison of
sample evaluations.

It supports a candidate 69-operation, degree-111 evaluator of the inherited
15-positive-variable equation. The initial 68-operation estimate missed
the old evaluator's shared multiplication `Δ*f²`; the corrected ledger was
emitted and checked independently. Compiler correctness and its connection to
ZFC have not been inferred from this local theorem.

`ShortSystem.lean` and `ShortFrontier.lean` now also check the 75-operation,
degree-68 and 73-operation, degree-80 alternatives. Both retain exactly the
complete positive zero set of P67. The Lean certificates include their
actual polynomials, literal evaluator identities, and degree upper bounds.
Independent finite audits establish the exact degrees, operation ledgers,
and nonzero leading coefficients. See [SHORT_SYSTEM.md](SHORT_SYSTEM.md)
and [SHORT_FRONTIER.md](SHORT_FRONTIER.md).

The literal circuit and finite ledger have now been emitted and independently
checked: 69 live binary gates, 40 multiplications, 15 additions, 14
subtractions, 15 positive witnesses, and exact degree 111. The selected
nonzero degree-111 monomial has coefficient `8*beta^64`. `ShortCircuit.lean`
includes the actual circuit evaluator, its integer multivariate polynomial,
the evaluation bridge, and equality of its complete positive zero set with
the literal P67 baseline. See [SHORT_EQUATION.md](SHORT_EQUATION.md).

## Exact refutation semidecider

`Computability.lean` shows each arithmetic operation of `EnumPerm.enumStep`
primitive recursive, proves its bounded iteration primitive recursive, and
searches for its first halting bound. `Bridge.lean` composes the existing
calculus-to-ZF and ZF-to-ZFC refutation equivalences. The resulting set
`zfcRefutationInputs` is the constant predicate
`BProv ZFCax_s [] Form.fBot`; its RE proof uses the literal enumerator.

Both new modules compile cleanly. Axiom audits of `refutationInputs_re`,
`halts_iff_refutation`, and `zfcRefutationInputs_re` list only `propext`,
`Classical.choice`, and `Quot.sound`. No consistency assumption is used.

## Checked external consistency equivalences

`Polynomial.lean` fixes the ordinary Jones input to 1 and proves that this
specialization does not raise total degree. `ZFC.lean` now composes this
with the actual refutation semidecider. It provides:

* `zfcNinePolynomial : MvPolynomial (Fin 9) ℤ`, with a natural zero iff
  `BProv ZFCax_s [] Form.fBot`;
* `zfcQuarticPolynomial : MvPolynomial (Fin 58) ℤ`, with total degree at
  most four and the same solvability equivalence;
* the negated equivalences to the syntactic `ConZFC` definition.

These modules and the umbrella import compile cleanly under `lake env lean`.
Both consolidated audit files pass and list no axiom beyond `propext`,
`Classical.choice`, and `Quot.sound`. This is a checked external Lean
equivalence about ZFC's actual syntax. The object-language ZFC derivation
remains open. The separate explicit route
has now closed the coefficient-recipe obligation: see
[EXPLICIT_EQUATION.md](EXPLICIT_EQUATION.md) and [DIRECT_PROGRAM.md](DIRECT_PROGRAM.md).
Its enormous numerical coefficient payload has not been materialized.
