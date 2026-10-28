# Proof simplifications, continued 28 October 2026

Two reviewed commits reduce the maintained Lean source and checks by211
lines. The reviewed series advances from4155 to4366; these counts include
new modules and the31-line compatibility test. All25 scoped final Lean
calls pass, and all121 old public axiom reports are byte-identical. The
original equations, constants and premises are retained.

## Reuse the supplied enumerator program

`59616d9d46` adapts zy's realizer dependency inversion. The existing literal
scalar program already realizes the bounded halting test at every input.
The computability proofs now use that property rather than repeat the
primitive-recursive constructions for arithmetic, states and enumerator
steps. A lower `EnumeratorSemantics` module carries the original run,
initial state, refutation predicate, halting test and semantic bridge.
`DirectScalarEnumeratorCore` carries the original program implementation.
The original `DirectScalarEnumerator` import remains a wrapper over
`Computability`, preserving its former transitive public names without an
import cycle.

The complete old production files total608 lines; all four resulting
production modules total395, removing213. A permanent31-line regression
imports only the old wrapper, reconstructs the legacy run/state/test source,
checks all-input equality by `rfl`, and checks the actual scalar program's
property and previously visible computability declarations. Including this
test gives182 net lines removed. The old four semantic definition bodies,
three private semantic bridge proofs, private encoding-instance source,
five Computability theorem headers,48 direct-program declarations and
Bridge source are literal. This source comparison does not claim identical
compiled private names or a particular typeclass-instance selection.

Six baseline calls check the three original modules, semantic/import probes
and62 old public declarations. Fifteen final calls check the nine-node
selected reverse dependency cone, both probes, the old public audit, the new
permanent regression and the decimal-machine ZFC endpoint with its existing
focus. Every call exits0; the62 old reports are byte-identical, including18
axiom-free declarations. No final warning or source-option increase is
introduced. The two decimal endpoint calls are additional to the original
seven-root graph; unchanged project/package dependencies remain precompiled.
This is not a whole-project or new upstream HA replay.

`sync_audit` independently reads the original and resulting implementations,
checks the compatibility import, verifies the scalar-program source recipe,
reconstructs the selected239-node graph and its nine affected nodes, and
checks the retained command/axiom observations without executing a compiler.
ROOT independently checks the source blocks, logs and every old report.

## Pell, margin and interval proofs

`1e173a6849` reuses an existing nonzero-ordinate lemma in
`NativePellBootstrap`, the positive-factor and square bounds in
`MarginSeparation`, and integer induction in `WangTiles942ResetRows`.
The arguments retain arbitrary ordinate signs, the original cap and interval
guards, both interval directions and all existing source data. The full
modules657→648,141→133 and162→150 remove29 lines/1099 bytes without
helper/import overhead. Every byte outside the three proof bodies is literal.

Seventeen original Wang preparation, target, client and focus calls, two
other original targets and a fresh59-declaration audit pass before editing.
Ten final target, client,
focus and audit calls pass on the first attempt without warnings. All59 old
reports are byte-identical, including five axiom-free declarations. Existing
checks cover negative seeds, both propagation directions, singleton
interiors, seam exclusion and the actual margin/Pell interfaces.
`sync_audit` independently reads all original modules, changed proofs,
underlying lemma contracts and focused controls, and authenticates all30
actual command observations and the full audit. Its graph check establishes
that this selected dependency closure does not intersect the enumerator
refactor. No reviewer compiler run is claimed.

The [evidence bundle](lean-proof-simplification-20261028-continuation-evidence/BUNDLE.json)
pins the source comparisons, baseline and final receipts, compiler logs,
timings, focused probes and dependency graphs. Its archive has144 entries;
ROOT checks every entry against its retained bytes and verifies archive
integrity. The original source snapshots preserve the historical inputs for
records whose module paths now refer to the changed files.

## South-word shifts

`9602a7db90` specializes the existing binary-prefix and copy-translation
lemmas for offsets19 and20. Both statements retain the nine physical copy
equalities, Boolean bound, remainder guards and selectors940/941/942. Every
byte outside the two proof bodies is literal. The complete module162→144
removes18 lines/615 bytes without helper/import overhead.

The exact supplied candidate failed because its literal additions and powers
were not reduced; the first repair also failed because natural casts remained.
The accepted proof explicitly normalizes those expressions. Both actual
exit-1 results and their exact sources are retained. The accepted target,
`CurrentWholeField2011` client, existing focus and eight-public audit all
pass without final warnings; every old report is byte-identical.

The original target and fresh baseline were checked after36 affected
prerequisites of the selected target, client and focus were refreshed in dependency order. Two earlier preparation
drivers were stopped after their running Lean commands completed: eight
successful preliminary calls are recorded, and the dependent ones were
repeated after the Bootstrap change. No Lean process was interrupted.
Existing prerequisite warnings remain in `CurrentMasks2011` and
`NativeBinaryScale`; they are separate from the final suite. The selected
116-source graph otherwise reuses unchanged objects and the installed
package boundary. No whole-project replay is claimed.

`sync_audit` independently checks the full original/final sources, both
proof contracts, actual status/log/time records and all eight old reports
without running a compiler. ROOT also checks the unchanged bytes outside
both proofs and authenticates the36 refreshed, two baseline, two failed and
four final command records. Historical source snapshots and observations
are preserved in [the South-word evidence bundle](lean-proof-simplification-20261028-south-evidence/BUNDLE.json).

Together with the earlier two commits, this continuation removes229 net
lines and advances the reviewed series to4384. All29 accepted scoped final
calls pass and all129 old public axiom reports are byte-identical. The
equation TeX/PDF remain unchanged, and the iterative goal remains active.
