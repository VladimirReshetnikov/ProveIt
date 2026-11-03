# iPRA endpoint for the ten-positive 75/402 equation: plan and status

**Target.** Native, standard and equality-only iPRA equivalences between the
no-positive-zero sentence of package 163's
[`trace75_degree402`](../../con-zfc-diophantine-forms/163-trace-radical/compact/equations/trace75_degree402.json)
equation and the selected Foundation ZFC consistency predicate. That
equation has ten strictly positive unknowns, 75 operations and exact degree
402, and sits on the delivered frontier.
[Its proof](../../con-zfc-diophantine-forms/163-trace-radical/compact/PROOF.md)
is ordinary mathematics; no Lean proof of its Con(ZFC) equivalence existed
before this campaign, even externally. Vladimir chose this target on
3 November 2026.

The route is the one used for the nine-variable equation: prove a
`PolynomialBridge` (in every model of `𝗜𝚺₁`, a positive zero exists iff
machine 215 halts) and apply `IPRAExpressionNative.equivalence_of_bridge`.
The bridge splits into a **kernel** part, specific to this equation, and a
**source** part, shared with other equations on the same tuple.

Sizes are proposed-work estimates in modules, not commitments.

## The source dependency (compact44 tuple)

The equation uses the compact44 tuple `beta = 2^590069 - 1, K0, MC, MF`
(directly indexed BFS943 radix67), not the 2011 tuple of the maintained
14-variable equation. Its "native outer endpoint" is therefore calibrated
on compact44:

```
X = 2^R,  q³ | Y,  t = B/h ≥ 0,  (K0 + Wbase) C − F = t (q − 1),  c = ψ_A(R),
first Pell witnesses with 0 < eta < k   ⇔   machine 215 halts.
```

The only Lean proof of a compact44 halt equivalence is in Codex's
`research/ordinary12-ipra-bridge` prototypes:
`CompactSymbolicModelUnconditionalIff.model_iff`, with an import closure
of 462 prototype modules. That lane is Codex's active coherent rebuild.
This campaign therefore states the source as an explicit hypothesis
(`SourceModel`, as in `IPRAExplicitZFCReduction`) and discharges it once the
compact44 rebuild lands in the tree. It does not rebuild those modules.

## Kernel stages (PROOF.md §§2–7, chart q3, weight L = V²)

| stage | content | existing Lean to reuse (generic in ports) | status |
|---|---|---|---|
| K0 | circuit value, ring identities (2.2), (3.1), (3.3) | — | **compiled**: `TenPositiveTrace75` |
| K1 | literal `Expr`, `evalRing` = value | — | **compiled**: `TenPositiveTrace75Syntax` (DAG never unfolded) |
| K2 | root extraction: `G = g²`, `E = tau²`, `F0 = f0²` from coprimality | `ModelDifferenceRing`, square-divisor lemmas | open |
| K3 | rational integrality of `y` in `QV² − (Q−1)y² = 1` | prototype only: `ReducedNormSigned.signed_denominator_divides` | open, port the generic statement |
| K4 | **signed all-index folding** ⇒ `c = ψ_A(p)`, `p` odd | **absent everywhere** | open; the central new proof (paper source: inherited Lucas parent) |
| K5 | first Pell classification, `n0 ≥ 2`, (3.5) | `ArithmeticPellFirstNorm.positive_parameter_solution` | open |
| K6 | exclusion of `p = 3`, `c > 4Delta + 3`; auxiliary index odd and ≥ 5 | `ArithmeticPellResidueClasses.odd_index_of_base_dvd`, `ArithmeticPellHalfIndex.y_three` | open |
| K7 | signed transport (4.3) and recovery `B ≥ 0`, `C > 0` | — | open |
| K8 | mask window `3q < R < q⁴` | `NativeAdaptiveRankWindow.target_window` (ℤ); `ArithmeticPellFirstIndex.scalar_window` (model) | open |
| K9 | normalized rank and `p = R` | `ArithmeticPellIndexDivisibility.relaxed_auxiliary`; `NativePellStepDown.source_index` (ℤ) | open; needs a model `source_index` |
| K10 | q3-chart integrality, uniform ratio estimate, projector ⇒ `X = 2^R`, `h ∣ B` | analogues only (`ArithmeticPellPowerRecovery`, `ArithmeticAdaptivePowerFinish2011`) | open |
| K11 | completeness: outer data ⇒ positive zero, via (7.1) and (7.2) | — | open |
| K12 | assembly: kernel iff + `SourceModel` ⇒ bridge ⇒ native/standard/reference endpoints | `IPRAExpressionNative.equivalence_of_bridge`, `IPRAStandardTheory.provable_iff` | open |

The kernel is first proved over `ℤ`, against the paper, then replayed over
`Facts R` and instantiated in `DiffRing V`, as for the carrier forms. K4 and
K10 are the largest new proofs (roughly 15–25 modules in all).

## Rules for this campaign

- **Builds:** one module per `lake build` (see the root `CLAUDE.md`).
- **Do not unfold the DAG.** Register equations are `rfl` lemmas
  (`TenPositiveTrace75.*_def`); `ring` runs over registers as atoms. A first
  version that unfolded the registers into the ten unknowns exhausted 7 GB.
- **Keep the kernel Foundation-free.** Kernel modules import neither
  Foundation nor Mathlib's matrices, so model-side and polynomial-side code
  can share them.
