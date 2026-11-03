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

**Kernel ordering boundary.** The retained trace75 JSON identifies its K0
payload by raw SHA-256
`0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f`,
the directly indexed BFS kernel. The existing `paramKernel rho` used in the
original-table compact model theorem has an externally reconstructed payload
with the different raw SHA-256
`c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e`.
See the [independent comparison](../../reviews/ten-positive-80-alignment-fresh-projection-independent/README.md)
and [direct-BFS kernel review](../../reviews/direct-bfs-lean-kernel-decoder-independent/README.md).
Thus the cited original-table model equivalence cannot alone discharge a
`SourceModel` for the trace75 K0: that requires a checked color/row and
packing transfer, or a separate proof for the direct kernel, as well as a
binding from the retained bytes to the Lean term. The current direct-BFS
[graph-to-halt route](../direct-bfs-80-model-halt-prototype/README.md) and
[converse packing work](../direct-bfs-completeness-route/README.md) do not yet
establish that complete `SourceModel` or a Lean file-binding theorem.

## Lane split (3 November 2026, Vladimir's decision)

Two agents work on this campaign. To avoid duplicate proofs:

- **Codex:** K2–K6 (already under way in `research/trace75-root-probe`),
  K8, K9, K12 and the compact44 source side.
- **Claude:** K7 (signed transport, `B ≥ 0`, `C > 0`), K10 (q3-chart
  integrality, ratio estimate, projector ⇒ `X = 2^R`) and K11 (constructive
  completeness), all **model-internal** (every model of `𝗜𝚺₁`), building on
  the trace75 register module `TenPositiveTrace75` and the conventions of
  `Trace75Factors`.

K6 was offered to Claude, but Codex had already reached it, so it stays with
Codex. A stage changes hands only when this section says so.

## Kernel stages (PROOF.md §§2–7, chart q3, weight L = V²)

| stage | content | existing Lean to reuse (generic in ports) | status |
|---|---|---|---|
| K0 | circuit value, ring identities (2.2), (3.1), (3.3) | — | **compiled**: `TenPositiveTrace75` |
| K1 | literal `Expr`, `evalRing` = value | — | **compiled**: `TenPositiveTrace75Syntax` (DAG never unfolded) |
| K2 | root extraction: `G = g²`, `E = tau²`, `F0 = f0²` from coprimality | `ModelDifferenceRing`, square-divisor lemmas | [graph roots](../trace75-root-probe/FACTORS.md) checked from an actual positive trace75 zero and positive beta; later Pell quotient and machine steps remain open |
| K3 | rational integrality of `y` in `QV² − (Q−1)y² = 1` | generic internal `AdjacentInteger` descent | [adjacent quotient](../trace75-root-probe/ADJACENT.md) checked from an actual positive trace75 zero and positive beta; no converse or machine theorem |
| K4 | **signed all-index folding** ⇒ `c = ψ_A(p)`, `p` odd | [generic folded recovery](../pell-generic-fold-rebuild/README.md) rebuilt with a direct arithmetic import; `TenPositiveFolding.folding` is a separate in-tree integer version | [odd ordinate recovery](../trace75-root-probe/FOLD.md) checked from an actual positive trace75 zero and positive beta, with [independent source/receipt audit](../../reviews/trace75-fold-independent/README.md); no converse or machine theorem |
| K5 | first Pell classification, `n0 ≥ 2`, (3.5) | `ArithmeticPellFirstNorm.positive_parameter_solution` | [classification](../trace75-root-probe/PELL.md) and [index-one exclusion](../trace75-root-probe/INDEX.md) checked for the actual unscaled trace75 parameter; the latter has an [independent source/receipt audit](../../reviews/trace75-index-independent/README.md) |
| K6 | exclusion of `p = 3`, `c > 4Delta + 3`; auxiliary index odd and ≥ 5 | `ArithmeticPellResidueClasses.odd_index_of_base_dvd`, `ArithmeticPellHalfIndex.y_three` | [main index `p ≥ 5`](../trace75-root-probe/MAINFIVE.md), [carrier bound](../trace75-root-probe/MAINSIZE.md), and [auxiliary index ≥ 5](../trace75-root-probe/AUXFIVE.md) checked for beta ≥ 2 from an actual positive zero; [auxiliary-index audit](../../reviews/trace75-aux-five-independent/README.md) records the witness scope; fixed-port specialization and index alignment remain open |
| K7 | signed transport (4.3) and recovery `B ≥ 0`, `C > 0` | [generic transport helpers](../generic-transport-rebuild/README.md) rebuilt without a direct 80-rank import; `TenPositiveTransport.transport` is a separate in-tree ring-generic version | [transport sign and old-chart mask](../trace75-root-probe/TRANSPORT.md) checked from an actual positive zero and beta > 0, with [independent audit](../../reviews/trace75-transport-independent/README.md); the new trace74 reverse guard is not established |
| K8 | mask window `3q < R < q⁴` | `NativeAdaptiveRankWindow.target_window` (ℤ); `ArithmeticPellFirstIndex.scalar_window` (model) | [rank binding and window](../trace75-root-probe/RANK.md) checked from a positive zero under beta ≥ 31 and explicit low/high mask bounds, with [independent source/receipt audit](../../reviews/trace75-rank-independent/README.md); K0 is arbitrary |
| K9 | normalized rank and `p = R` | `ArithmeticPellIndexDivisibility.relaxed_auxiliary`; generic [rank reduction](../pell-rank-generic-rebuild/README.md) | [rank exactness](../trace75-root-probe/RANKEXACT.md) checked for beta ≥ 31 and explicit mask bounds, with [independent source/receipt audit](../../reviews/trace75-rank-index-exact-independent/README.md); power recovery and machine bridge remain open |
| K10 | q3-chart integrality, uniform ratio estimate, projector ⇒ `X = 2^R`, `h ∣ B` | analogues only (`ArithmeticPellPowerRecovery`, `ArithmeticAdaptivePowerFinish2011`) | [offset divisibility](../trace75-root-probe/OFFSETDIV.md), rank congruence and [first/main index alignment](../trace75-root-probe/INDEXALIGNMENT.md) checked under explicit port bounds, with [alignment audit](../../reviews/trace75-index-alignment-independent/README.md); power recovery remains open |
| K11 | completeness: outer data ⇒ positive zero, via (7.1) and (7.2) | — | open |
| K12 | assembly: kernel iff + `SourceModel` ⇒ bridge ⇒ native/standard/reference endpoints | `IPRAExpressionNative.equivalence_of_bridge`, `IPRAStandardTheory.provable_iff` | open |

For the remaining K6 branch, [graph-derived index-two algebra](../trace75-root-probe/THREETWO.md)
gives the exact first-parameter and carrier equations and a signed eta identity
under the explicit main-index-three premise. A [subsequent contradiction](../trace75-root-probe/THREEEXCLUDED.md)
excludes that premise for an actual positive zero and a first-ordinate witness
when beta is at least two in the model. An [independent source and receipt
audit](../../reviews/trace75-three-excluded-independent/README.md) checks that
argument without replaying Lean. A subsequent [main-index composition](../trace75-root-probe/MAINFIVE.md)
combines it with the first- and odd-index witnesses; fixed-port specialization
remains open.

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
