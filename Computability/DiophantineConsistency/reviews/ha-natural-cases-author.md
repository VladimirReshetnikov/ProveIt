# HA zero-or-successor author receipt

The new packet proves the actual conventional-HA sentence
`∀x (x=0 ∨ ∃y x=S y)` using `HA.Arithmetic.induction`. It also derives
arbitrary term instances with capture-avoiding shifts under the existential
binder, and an explicit successor-predecessor witness. The finite-list
`Relative` disjunction and existential-introduction wrappers are direct
applications of the existing intuitionistic derivation constructors.

The base case uses reflexivity and the left disjunction introduction. The
successor case uses the present induction variable as the witness, then
introduces the right disjunction, implication and universal quantifier.
The induction hypothesis is unused in that branch. No excluded middle,
double-negation elimination, classical-provability conversion, standard-model
oracle, or C222/machine calibration is assumed. This is a bounded HA arithmetic
packet, not an HA consistency equivalence. Equality decidability is not added.

Frozen sources under `Lean/DiophantineConsistency/`:

| File | SHA-256 |
|---|---|
| `HANaturalCases.lean` | `7c1552f2f650238b04b7fc2fb142c2ab3aaf7885278f6e49aaaf66b8c5e1b1a3` |
| `HANaturalCasesChecks.lean` | `6b0026edd39c9d683ade5f3ee5efa7f7ec124525886c9bc8528074715d37d74d` |

I read the complete main and focused-check sources before execution. Checks
exercise variable 0 and variable 4, a nested arbitrary term, the exact zero
and successor substitutions, the explicit successor witness, sentence closure,
and reclosure of term parameters. All 11 final axiom reports contain only
`propext` and/or `Quot.sound`, or no axioms. There is no `Classical.choice`,
`sorryAx`, `native_decide`, or new axiom in this packet.

The only main import is `DiophantineConsistency.HABasicArithmetic`. Eight
custom prerequisite modules were reused after checking both current source
and exact prior object hashes: `FirstOrder.Fol`, `FirstOrder.Calculus`,
`FirstOrder.Completeness`, `PAHF.AckermannHFCore`, `PAHF.PASyntax`,
`HAProofs`, `HADeduction`, and `HABasicArithmetic`. The last uses the root's
independently replayed object from
`/tmp/ha-basic-arithmetic-root-peer-3xa84gxk/`. The five earlier central
source/object pairs and the HA proof objects retain the explicit provenance
of `ha-basic-arithmetic-dependency-replay.json` and the root replay pins.
This is a fresh two-leaf check over that authenticated cache, not a fresh
rebuild of every prerequisite or Lean's toolchain.

Both final builds ran directly with the authenticated Lean 4.32 compiler,
`-M6000 -j1 -DElab.async=false`, and `LEAN_PATH` equal only to
`/tmp/ha-natural-cases-author-sjurd49t/lib`. The new target objects were absent
from that private overlay. No shared object, existing source, umbrella,
package source or Git state was modified. Main exited 0 in 0.55 seconds with
an empty log; final checks exited 0 in 0.67 seconds with the 11 reports.
The first checks run failed only because the sentence-syntax check needed
explicit disjunction splitting before `omega`; that source/log is retained.
The main passed on its first run and was not changed afterward.

Final objects:

- Main: `7e7aeef7beb97e0a8747af6c5553d6d0f81232c756106bcf16f07265ebee5e1e`.
- Checks: `e889b09543b30eeab877b7bc0298f3c2e027ae65633f5cf3b8f1cacb75b8c484`.

The durable `ha-natural-cases-author-replay/` directory contains exact
pre-execution input pins, fully read preparation/build scripts, every source
snapshot, command, exit code and log. The aggregate
`ha-natural-cases-replay.json` has SHA-256
`13c15f5d4d44ffee2df2aa52a6cd00def3ae1830e5526b2604a9a785f57846b0`.
All prerequisite hashes were checked again after each invocation and at freeze.
