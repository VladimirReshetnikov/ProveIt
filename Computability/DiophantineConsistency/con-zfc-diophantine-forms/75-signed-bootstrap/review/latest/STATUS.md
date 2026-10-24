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
| Wave-8 proposals and current target | Reviewed; target switched again | Packages 54–59 at `beb0192cb8`; all six full finite replays PASS; package 59 adjunct has nine positive variables, 473 operations, degree 1,910,404; see `PROPOSAL_REVIEW_WAVE8.md` |
| Compact split-form coefficient instances | Generated and independently replayed | Whole package-54 / package-57 tuples, same 473 operations and degree 1,910,404; preferred sharp native payload 215,492 raw bytes and live derived constants 1,672,725 bytes; see `candidates/split116-compact/README.md` |
| Split-form generic source contract | Lean checked | Full binomial-to-bounded-source-coefficients equivalence, derived degree/quarter bounds, unconditional word positivity and exact outer ratio; native calibration remains separate; see `SPLIT116_FORMALIZATION.md` |
| Literal split116 source and unbounded nine-coordinate equivalence | Lean checked | `SplitNineSource59.exists_natural_zero_iff_source_compact54`: exact authoritative old-z source, all 89 kernel records, four explicit port boxes; no supplied height, degree, packing or population premise; see `SPLIT_SOURCE59.md` |
| Literal split116 nine-variable polynomial | Lean checked | `SplitNinePolynomial59`: actual `MvPolynomial (Fin 9) Int`, ring-map and natural evaluation identities, source-zero iff; counted-DAG identity remains separate |
| Shared split116 base powers | Generated and independently checked | Same polynomial in 456/463 positive/natural operations, 17 fewer; exact exponent/gate remap, unchanged constants and degree; Lean rewrite proof in progress; see `candidates/split116-joint-powers/README.md` |
| Signed native Pell step-down | Lean checked | `NativePellStepDown`: signed minus-form index recovery and safe strong-quotient restoration; recovered main sequence and bootstrap hypotheses remain explicit; see `NATIVE_PELL_STEP_DOWN.md` |
| Exact meaning of consistency | Identified | `¬ BProv ZFCax_s [] Form.fBot`; existing unconditional K215 endpoint |
| Concrete recursively enumerable refutation predicate | Lean checked | `Computability.refutationInputs_re` and `Bridge.zfcRefutationInputs_re`; actual six-register enumerator |
| Nine-variable specialization | Lean checked | `zfcNinePolynomial_noZero_iff_conZFC`, no premises; existence-based coefficients |
| Quartic alternative | Lean checked | `zfcQuarticPolynomial_noZero_iff_conZFC` and total degree at most four |
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
| Internal multiplication and natural expressions | Lean checked | Actual ZFC totality/functionality proofs in `ObjectMultiplication` and `ObjectNaturalExpression` |
| Actual polynomial-side object sentence | Lean checked | `ObjectEquation.unsolvabilitySentence`, exact semantics over all internal natural tuples; the internal consistency iff is still open |
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
