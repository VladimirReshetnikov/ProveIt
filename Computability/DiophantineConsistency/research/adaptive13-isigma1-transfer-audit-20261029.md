# Current adaptive 13/88/51: the missing all-model transfer

Read-only source audit by `circuit_reduction`, 2026-10-29. Snapshot:
`fa059b73ac170ec64631aee36a788a596c262471`, verified against `origin/main`
and `git ls-remote origin refs/heads/main`. This note proposes work; it adds
no Lean theorem, compiler replay, cache authentication, or new metric claim.
All Lean filenames below are under
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

## What is already proved

`HACurrentEquation2011` has four closed endpoints:
`isigma1_proves_current_iff_consistency`,
`isigma2_proves_current_iff_consistency`,
`peano_proves_current_iff_consistency`, and `ha_current_iff_consistency`.
The final leaf supplies both the actual source bridge and
`ArithmeticLocalNormalization.localNormalization`; it has no remaining
source, polynomial, or local-normalization hypothesis. These endpoints cover
**one literal equation**, the maintained Fin14 Carrier65 expression. Its
single positive shift is retained. The HA conclusion is
`ProofEquiv ArithmeticCurrentEquation2011.unsolvabilitySentence
 FoundationHAConsistencyNormalization.ordinaryConsistency`, where
`ProofEquiv a b := HA.Proves (.and (.imp a b) (.imp b a))`.
The consistency target is the ordinary negation of the actual Foundation
positive ZFC-refutation predicate. Its standard-natural meaning is bound to
`¬ SetTheory.BProv LeanProofs.BoundedZFCConsistency.ZFCax_s []
 SetTheory.Form.fBot` by `FoundationHAConsistencySemantics`.
The PRA statement in the endpoint's comments is not an additional Lean PRA
derivability theorem in this leaf.

The 13/88/51 candidate is `NativeAdaptiveCurrent2011.polynomial`, built from
`NativeAdaptiveGraph.polynomial currentPorts`. Its coordinates, in order, are
`J,F,alpha,f,i,T,X,Y,r,eta,zeta,u,gamma`. Its exact current ports are beta,
K, lowPort, and **highPort + beta**, with the fourth port shifted once.
The existing finite metric receipt is `reviews/adaptive-current13-metrics-root.md`:
88 live binary operations, degree51, nonzero leading coefficient
`-32*beta^15`, and the complete 47,313-byte current port payload. Those finite
metric results are separate from an all-model arithmetic theorem.

The exact external equivalence is
`NativeAdaptiveCurrent2011.current_positive_zero_iff_carrier` (line70):
`PositiveZero polynomial ↔ PositiveZero CurrentPolynomialWindow2011.polynomial`.
Here both existential assignments are over **ℤ**. Its generic version
`positive_zero_iff_carrier` (line34) assumes
`NativeSourceMask.Interface p d MC MF`, `MC % 4 = 2`, and
`Carrier65Witness.PortBounds p`. The fixed-current theorem discharges them.
`positive_zero_iff_not_conZFC` and `no_positive_zero_iff_conZFC` then compose
the external maintained-equation result. The source explicitly says this is
external Lean mathematics, not an HA derivation.

The two maps are substantive:

* `adaptive_zero_carrier_zero` uses
  `NativeAdaptiveGraph.positive_zero_source` (line303), then
  `NativeOrdinarySourceConstruction.source_constructs_carrier65`. It constructs
  a positive natural Fin31 source and rebuilds private Pell witnesses. It
  preserves J,F,alpha; it does not identify the private coordinates.
* `NativeAdaptiveCanonical.carrier_zero_adaptive_zero` (line311) first invokes
  canonical Fin15 restoration, then `canonical_adaptive_zero` (line154).
  Its assignment uses `i_adaptive = delta*i_parent`, the actual X,Y,
  `u_adaptive = y_parent - V`, and new positive r and gamma. Positivity is part
  of the proof, not an automatic consequence of the polynomial identities.

A search of the snapshot's current `Arithmetic*`, `HA*`, and `FoundationHA*`
Lean leaves found no adaptive candidate binding or transfer theorem.

## Exact intended new target and its domain

First bind a narrow literal `Expr (Fin 13)` to the accepted 88-operation DAG
and the same four current ports. Then define its positive zero by equality
of its two `splitNatural` evaluations, as the Fin14 sentence already does.
The intended theorem is, for arbitrary
`{V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`:

```
(∃ x : Fin 13 → V, (∀ j, 0 < x j) ∧
  adaptiveExpr.splitNatural.1.evalSemiring x =
  adaptiveExpr.splitNatural.2.evalSemiring x)
↔ ∃ v : Fin 14 → V, ArithmeticCurrentSentence2011.PositiveZero v
```

This is **positive-zero existence equivalence**, not a bijection of
assignments. All new Pell indices, powers, quotients, and witnesses must be
elements of V, possibly nonstandard. The algebraic `NativeAdaptiveGraph.core`
and `value_map` are generic over commutative rings, but their zero-set proof
is specialized to ℤ. An IΣ₁ natural-number model has truncated subtraction;
it is not a commutative ring to which that theorem can simply be instantiated.
The existing `ArithmeticSignedPairs` and split-natural syntax are the narrow
reusable representation. A new ordered ring completion is unnecessary.

## Recommended shortest route

This recommendation follows the inspected interfaces; it is not a proved
new transfer. Use the already finished internal machine/window bridge to
avoid reconstructing all 31 historical source coordinates.

1. **Literal adaptive zero to its four cuts.** Bind the exact syntax and
   derive `A0=0`, `A1=0`, `Fs=1`, `Fa=1` from
   `(1+A0)*(1+A1)*Fa*Fs=1`, representing signed expressions by pairs.
   The external reference is `NativeAdaptiveGraph.value_zero_iff_factors`
   (line256), `value_zero_iff_cuts` (line290), and `NativeAdaptiveUnitFactors`.
   Existing `ArithmeticNegativeNorms`/`ArithmeticSignedPairs` provide relevant
   finite sign and magnitude tools. The four adaptive exclusions must still
   be bound to these exact factors; the maintained five-factor lemma is not
   the same statement. This is the smallest useful first implementation pair.

2. **Adaptive cuts to internal scalar/window facts.** Port only the adaptive
   bootstrap around the already represented Pell library. Recover the scaled
   quotients, actual indices, X=`Exp.exp R`, q=`Exp.exp (94517*N)`, transport,
   and the population lower bound. Then expose a scalar client of the existing
   window proof and use `ArithmeticCellWindow.window_halts` (line41).
   `ArithmeticWindowInterface.window_of_equations` (line113) currently packages
   its input as a Fin14 vector plus all five equations; it is not already an
   adaptive API. Its transport/saturation/carry proof is reusable after a
   small interface factoring, with every actual mask premise derived.
   `ArithmeticCurrentConstruction2011.halt_positive_zero` with the accepted
   `localNormalization` then yields the maintained positive zero.

3. **Internal halt to adaptive positive zero.** Reuse the actual scalar
   packing/rank construction and the internal outer/auxiliary seeds, then
   apply an internal version of `canonical_adaptive_zero`'s finite coordinate
   identities and positivity bounds. `ArithmeticConstructionAssembly` already
   constructs `SeedRelations` and the auxiliary literal equality in its proof
   (lines245–290), but its public `construction` (line395) returns only the
   Fin14 vector and five equations. A narrow companion exposing the same
   constructed canonical data would avoid rerunning a standard-Nat source
   conversion. In particular prove the adaptive r, gamma-shift and y−V are
   positive; do not assume a merely arbitrary Fin14 witness already has the
   chosen canonical signs. Compose with `ArithmeticSoundness2011.zero_halts`
   (line22) for the reverse existential implication.

4. **Sentence/HA composition after the arithmetic theorem.** Bind the new
   positive-shifted no-zero sentence using the existing generic
   `FoundationHANoZero` machinery. Completeness supplies the source IΣ₁
   no-zero equivalence from the all-model theorem; the accepted arithmetic
   negative-translation/stability transfer supplies HA proof existence.
   No new source-ZFC, checker, machine, or Gödel–Gentzen algorithm is required.
   Neither the present ℤ theorem nor a standard-Nat semantic comparison can
   substitute for step2.

## Precise reuse and remaining mathematical work

The scaled bootstrap is the main remaining work, not a notation change.
`NativeAdaptiveCarrierBootstrap.first_carrier_integral_positive` (line21)
extracts M|Z from M²|Z², a signed first root, Y=q³s>0 and Bt=(q−1)b>0.
`NativeAdaptiveMainBootstrap.main_carrier_bootstrap` (line127) extracts the
scaled main root. Their current proofs use ℤ divisibility, abs, `.toNat`,
`.natAbs`, and standard `Pell.xn/yn`. Internal square-divisor cancellation,
ordered signed cases, and positive quotient bounds must be supplied.

`NativeAdaptiveRankWindow.adaptive_early_bounds` derives a source-free rank
window, n≥25, n<p, large c and half bounds. Its internal port can use:

* `ArithmeticPellClassification.solution_index` (line100), and
  `ArithmeticPellFirstNorm.solution_index`/`solution_residues` (lines74/142),
  with genuinely internal indices.
* `ArithmeticPellIntegralSolution.integral_solution`/`integral_solution_tsub`
  (lines90/125), replacing the standard relaxed-auxiliary theorem.
* `ArithmeticPellHalfIndex.half_index` (line380): the strong input is exactly
  `(i*c*c)^2 + delta = delta*f*f`, with explicit large-c, half-window, norm,
  and two `SignMod` premises. This fits the adaptive relaxed factor better
  than the maintained `literal_half_index`, whose input is stricter.
* `ArithmeticPellCongruences.first_difference_four` (line57), and the generic
  first/main-index comparison tools. `maintained_first_indices` is not
  directly callable before adaptive transport/scale/index facts exist.

`NativeAdaptivePowerProjection.adaptive_projection` (line85) obtains only
`q | 3*X` and `(4*a+3) | 3*(X-2^R)` initially. Three cannot be cancelled
unconditionally. `NativeAdaptiveFactorThree.cancel_factor_three` and
`NativeAdaptiveMersenne.mersenne_base_recovery` handle the possible 3|q case;
their current proofs remain ℤ/ℕ. Internal replacements can reuse
`ArithmeticRadixAlignment.exponential_factor`, `exp_mod_radix`, and
`aligned_exponent`, once their actual hypotheses are proved.

Power growth also needs care: `ArithmeticPellPowerRecovery.power_bound`
assumes X≥16, while adaptive X is initially only positive. The external
`NativeAdaptivePowerRecovery.adaptive_X_eq_two_pow` handles X=1 separately
and uses a sharper ratio estimate for X≥2. Applying the maintained bound
before proving its hypothesis would be circular. Its `maintained_power`
also assumes X=wq and the unscaled main root, both missing initially.

After the exact indices and powers, reuse
`ArithmeticHalfBinomial.half_binomial` (line61) and `population_lower`
(line116). The latter explicitly needs `Exp.exp (3*h) | Y` and
`3*h+1 ≤ 2*r+1`; these are obligations, not automatic from q|X.
For construction, `ArithmeticOuterSeed.outer_seed_with_size` (line50)
requires u>0, odd R and `population R=3*u+2`;
`ArithmeticPellAuxiliarySeed.auxiliary_seed` (line148) requires `R%4=3`
and supplies positive f,i,T,V,y and the exact equality
`f*f*c*T = V+c+f*f*R`. Actual construction already derives these premises.
The new coordinate map must retain them explicitly until discharge.

## Evidence boundary and source pins

This was source inspection and targeted searches only. No fresh Lean replay,
object/provider selection, dependency closure authentication, or compile-cost
estimate was performed. The remote advanced from e86753d to the pinned
fa059b73 during inspection; endpoint/adaptive statements were unchanged.
The intervening arithmetic changes factor common unary-recursion proofs.
The SHA256 table below hashes exact Git blob bytes, not compiled objects.

| Source | SHA256 |
| --- | --- |
| `HACurrentEquation2011.lean` | `b041f0815e52985a3c60eed5bed9648a62f1bfd5f495d72d2ce3797b94e71e3e` |
| `FoundationHAConsistencySemantics.lean` | `fd3b7765dd24c838f8fdc464598fa8ac7cd170c188547a75eab7f2d359301a85` |
| `FoundationHANoZero.lean` | `8539882d474478c041177ed90eae788ff02167a7c15621117287e4ab3904eb60` |
| `NativeAdaptiveCurrent2011.lean` | `f9cc2a38fa9734d5b468bff3a69f43f0f3f71fb89e0207f2bd91a85d1052defb` |
| `NativeAdaptiveCanonical.lean` | `a0c82bb2f48b1b5dc944f663ba4144ba3c4f9ab430e2dcab871e278083bae7a4` |
| `NativeAdaptiveGraph.lean` | `4b0e17f6e72a179c95450500bea12dd6fd770fb2a76ee5b2652c3080ff1413fc` |
| `NativeAdaptiveUnitFactors.lean` | `b9bc1883c478f5e236c32b7d06ab4d132a80b3fd55e317df0650e55c497447cb` |
| `NativeAdaptiveCarrierBootstrap.lean` | `0975b336fd452dff7c68a8ccb795c8af516c2c08dac6940542b0f148f2dc1761` |
| `NativeAdaptiveMainBootstrap.lean` | `a735876afcc033877741f414e233f1dea1bc9209899979fd83fc8308733eae7a` |
| `NativeAdaptiveRankWindow.lean` | `f536f9324408a9660967e62baf10f01d85ed45ef7e4619e1c9f32710c6bd9b52` |
| `NativeAdaptiveStrongIndex.lean` | `6e0e0a65b62defe5759f54eeb9a527a48a5d7d8ffb35021187930acb44098284` |
| `NativeAdaptivePowerProjection.lean` | `92a4d01435c031ea51706162503e5e51239c39eb5eebdfcaac587c933ef09c84` |
| `NativeAdaptiveFactorThree.lean` | `cf7ebc1c3af93eb4ca800f309c411445dd267d0bf7d3bda437620be6cc702a67` |
| `NativeAdaptivePowerRecovery.lean` | `cd97a608e86cefcba299f53f76150112c63898327f82460c7daf78b229d6f0ae` |
| `NativeAdaptiveMersenne.lean` | `555c1c5cf659d00499b1f7d0952483e9269754fd965f4f56aaa06d7e875a978c` |
| `NativeAdaptiveSourceRestoration.lean` | `d3dbdffe6ad47d9da540cccbc7017a8bb52bfc56901b38923d28ba74c84fbc08` |
| `NativeOrdinarySourceConstruction.lean` | `b40f896c329a6d93825beb396321bc558e19b3ea18275124f91e367fd0a0afda` |
| `ArithmeticSignedPairs.lean` | `ecad260baefecc05bab664a976015d7a76228583c7ec25bcc7536890ef58274d` |
| `ArithmeticNegativeNorms.lean` | `00c0a3b6bbddd9d6ea23d1e1ecbcc2e02f383a76e7618f6328288d413719d7ef` |
| `ArithmeticCurrentSentence2011.lean` | `10c1a2e92f05c9765e91fd872050b25c23a94754ec87a0122aebd2e4c90c13e6` |
| `ArithmeticCarrierSoundness2011.lean` | `c508ae2229ae91d79cf572947a8ab5383a5bc756f825054523932b79b4873105` |
| `ArithmeticPellClassification.lean` | `77dc61a25a075c237ea36cc14a3e46c9832a1de827b84427679e268111a4cf78` |
| `ArithmeticPellFirstNorm.lean` | `374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5` |
| `ArithmeticPellCongruences.lean` | `75e5e2c18b70a6cf9b4cdd0d1f8fe52bc3104c2ae34de5ff4169f5786885c6b1` |
| `ArithmeticPellIntegralSolution.lean` | `c07a7cf5afc0f753191010fd2b51d251c85ba4375dfa5c6b124f9851d158cea0` |
| `ArithmeticPellHalfIndex.lean` | `7703193660d8ae98408d1ec3a83f6f8811927252e739bb7af18dbafb833a8877` |
| `ArithmeticPellFirstIndex.lean` | `8cf79ed14f00f565accbfae0eb03ccacca597d06d12a509fecd6d3272e30f9ce` |
| `ArithmeticPellPowerRecovery.lean` | `636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390` |
| `ArithmeticRadixAlignment.lean` | `28275cde76bb21343e01af3bfd6f025e14e0159b66e05c7a34a9780b02c49c81` |
| `ArithmeticHalfBinomial.lean` | `14bf89e1dc754c5b5e232f3fd3dc50dd2db1963a535160f8449cc940862db4ac` |
| `ArithmeticOuterSeed.lean` | `cc45baaa9dd7782afad29edbbcb8199926b4d2b8161ff4cb71204eda8eb897dc` |
| `ArithmeticPellAuxiliarySeed.lean` | `c20a64d1587b74dc7f18c208ba6f96052cbcfbf29da8c0e2567551055501f773` |
| `ArithmeticWindowInterface.lean` | `5026471145aca946886f07fe32f82d5b3aca1bcb00875eb8f16a4e8bdf3c337d` |
| `ArithmeticCellWindow.lean` | `4e30504beb6105b21395a850fd96a779dae2146ff97a0445ee6fb5303d5eda20` |
| `ArithmeticSoundness2011.lean` | `cec40465c31c24b2c9db10e25bbd9c3b50bc2e808bc521a2f3fa5019fa7e7871` |
| `ArithmeticCurrentConstruction2011.lean` | `a3ca72629ddbd95656914e0137e2909f611553f99bb2a3a19c26d3a76a6b88fe` |
| `ArithmeticConstructionAssembly.lean` | `6b5d81f08c7c82708f9afb8db0d9d8bb3199d61f85e6c3f478f4a7354d8226d0` |
| `ArithmeticLocalNormalization.lean` | `5d0ac1625dd03ed79f50e9d71edac75bb14547f6f6961316769c887db31c905b` |

Metric receipt `Computability/DiophantineConsistency/reviews/adaptive-current13-metrics-root.md` SHA256: `ddfd728ed1e6f676a1af96b8a0cf2130e1657ddea825bef1e4e8a8184325694b`.
