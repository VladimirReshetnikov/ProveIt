# Current arithmetic transfers and the next internal-ZFC bridge

Read-only source audit, 26 October 2026. This note distinguishes the actual
length2011/942-tile equations from the older compiled equations and from
sentences in the repository's first-order ZFC calculus. It adds no Lean
theorem and makes no fresh-build claim for the audited prerequisites.

## The three thirteen-variable transfers already exist

The exact current tuple is
`CurrentMasks2011.ports K = [beta,K,lowPort,highPort+beta]`, with
`beta=2^(47*2011)-1`. The fourth port includes its one source-mask shift.
See [CurrentMasks2011](../Lean/DiophantineConsistency/CurrentMasks2011.lean),
`ports`, `interface`, and `lowPort_four` (lines169–195).

For `K=(CurrentKernel2011.K:Int)`, `CurrentKernel2011.K_pos` supplies the
only remaining coefficient sign needed by
[CurrentCarrierArithmetic2011](../Lean/DiophantineConsistency/CurrentCarrierArithmetic2011.lean):

- `portBounds K hK` proves beta>=31, K>0, 0<MC<beta and
  beta<MF_source<2*beta from the entire fixed mask definitions.
- `completes K hK v hv hz` (line60) returns **one** positive Fin13 assignment
  solving `polynomial69`, `polynomial70`, and `polynomial71` simultaneously,
  together with `ThirteenCarrierComplete.SameOuter v u`. It already
  discharges the exact `NativeSourceMask.Interface` and MC%4=2. Neither
  a tableau assumption nor a compatibility condition on the private seed
  is left to the caller.
- `restores K u hu hz` (line71) accepts a zero of any of those three forms
  and derives a positive zero of `polynomial65`. This direction needs no
  positivity assumption on K.
- `positive_zero_existence_chain K hK` (line123) and
  `positive_zero_65_iff_71 K hK` (line129) are the reusable existential
  interfaces. Negating them with `not_congr` gives the corresponding
  no-positive-zero equivalences. No duplicate witness theorem is needed.

`polynomial65 (CurrentKernel2011.K:Int)` is definitionally the maintained
`CurrentPolynomialWindow2011.polynomial`. Thus a new concrete Fin14 zero
can be passed directly to `completes`, or its existence can be passed through
the existing equivalences. The three profiles are the accepted13-positive
69-operation/degree174,70/140 and71/128 polynomials; the numeral in each
name denotes its operation profile, not a different variable domain.

The maps are explicit. In
[ThirteenCarrierComplete](../Lean/DiophantineConsistency/ThirteenCarrierComplete.lean),
`replace` (line127) sends the14-coordinate tuple

```
(J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma)
```

to `(J,F,alpha,f',i',T',s,w,n,eta,zeta,m',gamma)`, where the four private
inputs are newly proved positive Pell witnesses. `SameOuter` (line171)
preserves J,F,alpha,s,w,n,eta,zeta,gamma. Its generic
`polynomial_zero_completes` (line243) requires `PortBounds`, the actual
finite `Interface p d MC MF`, and **MC%4=2**, in addition to the positive
14-zero. Evenness alone is insufficient for that residue premise.

In [ThirteenCarrierSoundness](../Lean/DiophantineConsistency/ThirteenCarrierSoundness.lean),
`restored` (line224) inserts `z=G/b+1`, replaces the derived signed ordinate
by its absolute value, and changes the parent i to b*i, where b=beta*J.
The required divisibility, nonnegative G, and positive z are proved before
division. The three13 forms have the same entire positive zero set at the
same assignment, by `ThirteenCarrier.positive_polynomial_zero_sets`.

## External endpoints and the new arithmetic assembly

[Bridge](../Lean/DiophantineConsistency/Bridge.lean), line11, defines the
actual proposition:

```
DiophantineConsistency.ConZFC := not (BProv ZFCax_s [] Form.fBot).
```

It is not a definition in a namespace `Bridge`. The literal715-digit machine
has the closed external endpoint
[DecimalMachineZFC.blank_halts_iff_zfc_refutation](../Lean/DiophantineConsistency/DecimalMachineZFC.lean)
and its negated equivalence, with this same axiom predicate.
[WangTiles942Completeness](../Lean/DiophantineConsistency/WangTiles942Completeness.lean),
`existsMarked_iff_blank_halts` and `no_marked_word_iff_conZFC`, already close
the actual finite marked-language equivalence and allow independently large
widths and heights in the constructive direction.

[CurrentSoundness2011](../Lean/DiophantineConsistency/CurrentSoundness2011.lean)
already proves positive maintained14-zero -> actual blank halt -> syntactic
ZFC refutation. `conZFC_no_positive_zero` (line48) and
`conZFC_no_thirteen_positive_zero` (line57) are closed implications for all
four current frontiers, with no supplied source, window, or native premise.

The new [NativePositiveSourceConstruction](../Lean/DiophantineConsistency/NativePositiveSourceConstruction.lean)
provides the arithmetic converse from **explicit calibrated scalar Data**:
its population endpoint derives both outer/private Pell seeds and a positive
actual14 zero. The controller/rephasing composition must supply those scalar
equalities for the same packing. This note does not promote that generic
endpoint to an already-closed current consistency equivalence. Once the
concrete14 converse is composed, the13 transfer requires only the existing
interfaces above, not further Pell or machine work.

Older external endpoints such as `NativeZFC.noPositiveZero_iff_conZFC`,
`ExplicitZFC.noNaturalZero_iff_conZFC`, and
`DirectQuarticZFC.noNaturalZero_iff_conZFC` concern their own literal compiled
polynomials. Their existence does not identify the current fourteen- or
thirteen-variable formulas.

## The internal target is a different theorem

The desired internal result for the maintained equation has the form

```
BProv ZFCax_s []
  (fIff ObjectCodeSeal.consistencySentence CurrentNoPositiveZeroSentence).
```

`CurrentNoPositiveZeroSentence` here is a **proposed** name, not an existing
constant found by this audit. The existing
[ObjectEquation.unsolvabilitySentence](../Lean/DiophantineConsistency/ObjectEquation.lean)
uses `ExplicitZFC.expression`, the older nine-variable natural equation.
It must not be silently substituted for the maintained equation's sentence.

The available [ObjectPolynomial](../Lean/DiophantineConsistency/ObjectPolynomial.lean)
API supplies `equationForm`, `noZeroForm`, and exact satisfaction on every
model's internal omega, for an actual finite `Expr`. The smallest useful
new packet is therefore a literal current expression with checked evaluation
and four-port binding, plus the domain conversion. One precise choice is
to encode `P(x_0+1,...,x_13+1)=0` on internal naturals; its no-natural-zero
sentence represents no positive zero of P. The existing `Expr.positiveShift`
uses x-1 in the opposite direction and should not be copied with the wrong
sign. A direct positive-input guard is another valid choice. This syntax
packet alone would not establish the consistency calibration.

[ObjectCodeSeal](../Lean/DiophantineConsistency/ObjectCodeSeal.lean),
`SealedRefutation` (line145), `consistencySentence` (line167), and
`sat_consistencySentence_iff` (line172), already describe arbitrary internal
sealed-axiom contexts and derivation certificates. Its
`sealedRefutation_of_external` quotes external derivations internally;
`conZFC_of_sat` is only an external consequence of internal satisfaction.
There is no converse extracting every nonstandard internal proof as an
external Lean derivation.

The substantive missing semantic theorem is an equivalence, **in every
model of ZFC**, between an internal sealed refutation and an internal
positive solution of the current literal polynomial. Equivalently, prove
the displayed `BProv` theorem directly. The external Lean iff over standard
Nat/Int, even once complete, does not supply this theorem. Numeral agreement
and a family of bounded-consistency proofs do not handle nonstandard proof
codes, witnesses, trace lengths, or Pell indices.

## Strongest reusable object-language results and next decomposition

- [ObjectArithmetic](../Lean/DiophantineConsistency/ObjectArithmetic.lean)
  and [ObjectMultiplication](../Lean/DiophantineConsistency/ObjectMultiplication.lean)
  have actual ZFC derivations of internal addition/multiplication totality
  and uniqueness. `ObjectNaturalExpression.evalForm_spec`,
  `zfc_proves_total`, and `zfc_proves_unique` cover supplied finite syntax.
- [ObjectQuarticCompiler.zfc_proves_compiler](../Lean/DiophantineConsistency/ObjectQuarticCompiler.lean),
  line100, is already an unconditional derivation in sealed ZFC of the
  source/compiled no-zero equivalence over the entire internal omega.
  `ObjectResidualSquares.zfc_proves_residual_conjunction` likewise proves
  the literal conjunction-to-one-polynomial step. These do not internalize
  an arbitrary external MRDP representation or the current native compiler.
- `ObjectPairingGraph`, `ObjectPairingSurjective`, and `ObjectUnpair` supply
  actual internal pairing totality, functionality, surjectivity and inverse
  uniqueness; the small arithmetic syntax gadgets also work on internal
  naturals. These are genuine reusable pieces, not the full proof checker.
- [AnnotatedRefutationPR.exists_refutation_iff](../Lean/DiophantineConsistency/AnnotatedRefutationPR.lean),
  line112, supplies a literal primitive-recursive sealed-ZFC checker and
  an **external** exact acceptance/refutability theorem. It is a possible
  internalization starting point. Replacing the current215-state machine
  by this checker would still require a proved relation for the same
  maintained equation; its external correctness is not that relation.
- [FirstOrder.Completeness.completeness_inf_context](../../../Logic/FirstOrder/Lean/FirstOrder/Completeness.lean),
  line1082, turns validity in **all** models of the sentence theory into
  actual `BProv`. `ObjectQuarticCompiler` demonstrates this route. The
  hypothesis is not merely validity for standard natural-number inputs.

After the literal current syntax/domain packet, separate the required work
into: (1) internal sealed-refutation/actual-machine computation semantics;
(2) internal native encoding and arithmetic/Pell witness transformations,
including their totality for internal indices; (3) composition of the two
arbitrary-model equivalences and first-order completeness. An alternative
direct proof-certificate translation must establish the same unbounded
claims. No generic theorem translating arbitrary existing Lean Nat proofs
into this object calculus was found in the inspected interfaces.

`BoundedZFCConsistency.Endpoint.zfc_proves_conZFC_unfolded n` proves each
external numeral's bounded consistency sentence. It is not a proof of the
universal consistency sentence or of the missing polynomial equivalence.
The maintained [OBJECT_ZFC.md](../OBJECT_ZFC.md) and
[LEAN_EQUIVALENCE_PLAN.md](../LEAN_EQUIVALENCE_PLAN.md) explicitly preserve
this distinction; this audit does not change either document.

## Read-time source pins

| Source | SHA-256 |
| --- | --- |
| `CurrentCarrierArithmetic2011.lean` | `5f749fdfe0a3857c6d84b0505574f1b1d09f5b859167659a34b04ba392f4a5b3` |
| `ThirteenCarrierComplete.lean` | `5f971560bae4ca88ba157fcb8a398e6f3f0bf418cd70491051c69bb8bf278fc0` |
| `ThirteenCarrierSoundness.lean` | `50478151e2e94dcdf150838df7a60660ce93dfb57fb6bea03e0251e8801687ce` |
| `CurrentSoundness2011.lean` | `1118ee3f50dffa046e1205b72a8cac84ef02b5cad0862ef53b79cde1de4ba7ef` |
| `ObjectCodeSeal.lean` | `d6c03115873d654745e140146ceace001d171d310e19f113ebb8056ed488d15a` |
| `ObjectPolynomial.lean` | `24a3ceece62501d1f40413444530d30d1961d1909ad1d941c8879a79d496cf2b` |
| `ObjectEquation.lean` | `3f3c0f79a17e495c0e5243ca8b31521eb1d26af4a1891b5426e88f9bf10f7066` |
| `ObjectQuarticCompiler.lean` | `4b86b03dea9c3427c32bd61ae901de681f087986fe1f09fa06eda501b8847ee7` |

This audit author wrote several reused arithmetic modules, including the
fresh private and outer seed constructions, and has not represented this
note as an independent revalidation of those own proofs. No existing file,
compiled object, or git state was changed for this audit.
