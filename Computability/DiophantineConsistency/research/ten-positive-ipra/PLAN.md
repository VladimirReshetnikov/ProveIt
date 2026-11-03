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

## Current proof boundary

For the direct-BFS symbolic ports, the independently reviewed
[model-halting client](../trace75-bfs-model-halt-prototype/README.md) proves
that every positive trace75 zero yields an internal machine halt in each
`IΣ₁` model. Its provider incorporates the independently audited
[14-stage fresh-provider replay](../trace75-fresh-provider-rebuild/README.md).
This is the zero-to-halt direction. The earlier baseline, supplements and
package/dynamic ancestry remain inherited.
The direct-BFS symbolic kernel is not yet formally identified with the
retained JSON/gzip coefficient bytes.

For the converse, the [natural-parts client](../trace75-natural-parts-binding-prototype/README.md)
constructs a positive trace75 zero from explicit same-valuation Pell and
carrier equations. The [unscaled reverse-data construction](../trace75-unscaled-reverse-data-prototype/README.md)
now supplies a coherent candidate tuple with the required `XY` carrier
multiplier, under explicit first-Pell, phase, power and size hypotheses. The
[reverse graph client](../trace75-unscaled-reverse-graph-prototype/README.md)
binds that tuple to the actual registers, and the [packing client](../trace75-packing-reverse-graph-prototype/README.md)
derives its assumptions from one compact packing and explicit seed conditions.
An exploratory [halt client](../trace75-bfs-halt-graph-prototype/README.md)
now derives the conditions from an internal halt and model-cast ports, and
the [model-iff client](../trace75-bfs-model-iff-prototype/README.md) joins both
directions at the stated symbolic natural ports. These clients use a mixed
historical-provider overlay with five recorded object differences. Moreover,
the earlier fresh trace provider replaced eight BFS baseline objects in the
halt-seed closure. Those exploratory clients did not establish compatible ancestry;
the [compatible-provider plan](../trace75-bfs-compatible-provider-plan/README.md)
records the affected cone. A [31-stage compatible trace replay](../trace75-bfs-compatible-provider-rebuild/README.md)
and [13-stage reverse replay](../trace75-bfs-compatible-reverse-rebuild/README.md)
have since passed and preserved the captured BFS halt-seed closure. The
[21-stage forward replay](../trace75-bfs-compatible-forward-rebuild/README.md)
has also passed and preserved the reverse and BFS closures on the same union.
The [five-stage final assembly](../trace75-bfs-ipra-final-assembly-plan/RUNNER.md)
then rebuilt the syntax, model iff, parameterized and fixed iPRA clients on
that union, passed the actual outer exit, and received an independent result
audit. It establishes the named native, standard and equality-only
proof-existence statements for the fixed symbolic expression, with mapped
refutation negation or the selected translated consistency sentence. Four
affected baseline objects have a separate [direct-producer audit](../trace75-baseline-four-provenance/README.md);
their upstream transitive ancestry, other unrebuilt ancestry and package/dynamic
inputs remain inherited. An independently reviewed [source inventory](../trace75-cone-source-inventory/README.md)
records the captured 186-module impact cone and a topological order. A separate
[141-input triage](../trace75-upstream-141-inventory/README.md) classifies its
direct outside-cone project selections. An independently audited
[19-producer check](../trace75-upstream-19-provenance/README.md) compares their
recorded explicit direct `.olean` inputs; implicit `Init`, companions and
package/dynamic history remain outside that check. Complete producer-time and
transitive ancestry and a source-current replay remain open.
The [decimal display](../trace75-bfs-decimal-display/README.md) has
external graph, coefficient, source-transcription and exact-degree checks,
not Lean semantics for external files.

## The source dependency (compact44 tuple)

The equation uses the compact44 tuple `beta = 2^590069 - 1, K0, MC, MF`
(directly indexed BFS943 radix67), not the 2011 tuple of the maintained
14-variable equation. Its "native outer endpoint" is therefore calibrated
on compact44:

```
X = 2^R,  q³ | Y,  t = B/h ≥ 0,  (K0 + Wbase) C − F = t (q − 1),  c = ψ_A(R),
first Pell witnesses with 0 < eta < k   ⇔   machine 215 halts.
```

An original-table compact44 model equivalence exists in
`CompactSymbolicModelUnconditionalIff.model_iff`. A separate
[direct-BFS 80-row model equivalence](../direct-bfs-80-model-iff-corrected-prototype/README.md)
has since been checked under its four symbolic port equalities. Neither is by
itself the trace75 source equivalence: the former has a different kernel
ordering, and the latter concerns another graph. The actual trace75 forward
direction and its current converse obligations are described above.

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
establish the trace75 converse or a Lean file-binding theorem.

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
| K6 | exclusion of `p = 3`, `c > 4Delta + 3`; auxiliary index odd and ≥ 5 | `ArithmeticPellResidueClasses.odd_index_of_base_dvd`, `ArithmeticPellHalfIndex.y_three` | [main index `p ≥ 5`](../trace75-root-probe/MAINFIVE.md), [carrier bound](../trace75-root-probe/MAINSIZE.md), and [auxiliary index ≥ 5](../trace75-root-probe/AUXFIVE.md) checked for beta ≥ 2; fixed-port bounds and later index alignment are checked separately |
| K7 | signed transport (4.3) and recovery `B ≥ 0`, `C > 0` | [generic transport helpers](../generic-transport-rebuild/README.md) rebuilt without a direct 80-rank import; `TenPositiveTransport.transport` is a separate in-tree ring-generic version | [transport sign and old-chart mask](../trace75-root-probe/TRANSPORT.md) checked from an actual positive zero and beta > 0, with [independent audit](../../reviews/trace75-transport-independent/README.md); the new trace74 reverse guard is not established |
| K8 | mask window `3q < R < q⁴` | `NativeAdaptiveRankWindow.target_window` (ℤ); `ArithmeticPellFirstIndex.scalar_window` (model) | [rank binding and window](../trace75-root-probe/RANK.md) checked from a positive zero under beta ≥ 31 and explicit low/high mask bounds, with [independent source/receipt audit](../../reviews/trace75-rank-independent/README.md); K0 is arbitrary |
| K9 | normalized rank and `p = R` | `ArithmeticPellIndexDivisibility.relaxed_auxiliary`; generic [rank reduction](../pell-rank-generic-rebuild/README.md) | [rank exactness](../trace75-root-probe/RANKEXACT.md) checked for beta ≥ 31 and explicit mask bounds; see [audit](../../reviews/trace75-rank-index-exact-independent/README.md) and the subsequent fresh-provider replay |
| K10 | q3-chart integrality, uniform ratio estimate, projector ⇒ `X = 2^R`, `h ∣ B` | [weighted product height](../trace75-root-probe/PRODUCTHEIGHT.md) and arithmetic Pell growth | [X = 2^R](../trace75-root-probe/GRAPHPOWER.md) and [natural transport with `B = h*t`](../trace75-root-probe/NATURALTRANSPORT.md) checked under explicit port bounds. The affected chain was subsequently replayed on the fresh provider; inherited baseline and outside-ancestry limits remain |
| K11 | completeness: outer data ⇒ positive zero, via (7.1) and (7.2) | [unscaled reverse data](../trace75-unscaled-reverse-data-prototype/README.md) and [natural parts binding](../trace75-natural-parts-binding-prototype/README.md) | conditional pieces checked; actual register binding and halt-derived inputs remain open, with historical reverse-data ancestry inherited |
| K12 | assembly: kernel iff + `SourceModel` ⇒ bridge ⇒ native/standard/reference endpoints | `IPRAExpressionNative.equivalence_of_bridge`, `IPRAStandardTheory.provable_iff` | [fixed-port endpoints](../trace75-bfs-ipra-final-assembly-plan/RUNNER.md) replayed and independently audited on the compatible union; inherited ancestry and external-file semantics remain open |

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
