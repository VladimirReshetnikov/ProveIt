# Actual operational updates and exact local signal receivers

Date: 2026-10-26. Independent full source/check reviewer and fresh replay:
ROOT. Author receipts: [machine step](wang-machine-step-author.md),
[actual action](wang-machine-action-author.md), [signals](wang-tiles942-signals-author.md).

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| WangMachineStep.lean (125 lines) | 479ef25344a09804f3eeb6bd980e947941af55965ac48291349f90de14c3f100 |
| WangMachineStepChecks.lean (87 lines) | 7857b6376beb1fa12c47f4f4cb8f550edb666394d2f524e772a92d1e0fc73cf6 |
| WangMachineAction.lean (119 lines) | 1776d84d82ae32ec58287779e639ce163bf0e10dec24056effc3aa4c2f1d3bd5 |
| WangMachineActionChecks.lean (98 lines) | f34414842cee2e898bd17712d5db800ca527d6408b1bb7be7328afac3bfe062c |
| WangTiles942Signals.lean (128 lines) | c678e98715e3ef8fa32f179275ba299f3d49256176510821c17056686ba76650 |
| WangTiles942SignalsChecks.lean (86 lines) | 01aae495b5eb8645d783473ebce3f21c2c68283a5641db6987864689988a0db9 |

All six complete frozen files were read before fresh direct root runs
with `lake env lean -M6000 -j1`. All passed; main outputs were separate
temporary objects and checks imported frozen author-built main objects.
The three main logs are empty and all thirty-five axiom audits contain
only standard axioms or no axioms. No complete dependency or umbrella
rebuild is claimed.

The operational update moves one cell, writes only at the old head and
reads the original destination bit at the new head. Its complete color
formula keeps the action's optional next state; entering halt still
performs the write and movement. Synthetic tests distinguish old and new
head cells, erasure and writing, both halted colors and unchanged remote
cells.

The actual action bridge authenticates the cache index2*q+b against the
literal decimal machine definition. It exposes write, movement and next
head color uniformly. Actual directional target membership proves the
bound<216, making215 exactly halt; a negative test shows why the same
state-number identity would be false for invalid target216. No second
unbound action table or decimal reevaluation is introduced.

Plain-input paired edges must be zero: their possible positive edges lie
in disjoint left and right rail ranges. A transition's real active rail
instead forces the correct adjacent receive tile and its exact target,
using injectivity only on the corresponding actual target set. Both
directions and halt215 are retained. Small edges below6 force zero, so
seam colors cannot absorb a receive signal. Zero edges still allow pass
or finish; pass is selected only with an explicit nonfinish hypothesis,
later supplied by the operating-row theorem.

These are exact operational and local-language components, without a
supplied tiling/run calibration, whole-row uniqueness or desired
consistency equivalence. The complete next-row proof, eventual halt,
converse/controller and internal-ZFC derivation remain further work.
Decimal equation display and metrics are unchanged.
