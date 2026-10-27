# ArithmeticCommandWordPerm222: independent review and replay

Verdict: **PASS**, with no requested source changes. This review covers the
literal raw-tail parser and its model/Nat graph bindings. It does not establish
an internal enumerator run, compiler correctness, consistency calibration, or
an HA proof of the target equivalence.

I authored neither of the two reviewed leaves. I read all 104 main lines and
30 check lines, the entire author driver `/tmp/wordperm222-root-build.py`, the
author's final and failed run records, the final source snapshots and logs,
and the relevant complete `ArithmeticCantor` definitions/proofs and actual
`EnumPerm` source. I inspected the explicit 101-module/37-external import
selection and rehashed its current source/object records. I did not repeat a
mathematical review or fresh compilation of the whole prerequisite closure.

## Frozen files and source binding

| File | SHA256 |
| --- | --- |
| `Lean/DiophantineConsistency/ArithmeticCommandWordPerm222.lean` | `e871fd138de904e667803864882b80981a4cd3dcdc2416bfe7b9a76211cc3a7c` |
| `Lean/DiophantineConsistency/ArithmeticCommandWordPerm222Checks.lean` | `cf96f36c2de2c88d650695e77d37d7b93ade1af915526be7f3ee9225d699ee89` |
| Actual `BusyBeaver.ZFC.ArithmeticCantor` source | `aadfdeb41e75c1652b555ed996fea5d15d7f1b9f65c7c553823a99773ee24c84` |
| Actual `BusyBeaver.ZFC.EnumPerm` source | `0c2a214ef68b37cb4df92c9a208d069bd2b4fca04f062483dfd11dc2b2a9e30e` |

`tailValue` follows the actual command permutation: opcodes zero and one
consume no operand, two consumes one operand, and every opcode at least three
consumes two operands. The literal AX packing is `P (c+3) (P y (P x r))`:
the y-then-x order is preserved. No old C254/other-opcode parser is substituted.

The bounded formula `tailDef` quantifies the first projection, first residual
pointer, and (when needed) second residual pointer under the original input
bound. The inequalities follow from the actual Cantor projection bounds, so
there is no supplied decoder witness or standardness assumption. The third
residual output is fixed by the actual `secondDef`. In the two non-small-opcode
branches, the explicit inequalities `2 ≤ first z ≤ z` discharge the bounded
formula's side conditions. `tail_defined`, totality/uniqueness, and `tail_le`
therefore range over an arbitrary model satisfying the stated IOpen assumptions.
The bound is deliberately weak (`≤`), not an unsupported strict decrease at raw
zero.

`tail_pack_nat` checks each of the four actual command constructors with an
arbitrary rest pointer. `tail_nat` is stronger: it identifies the parser with
`(EnumPerm.decode z).2` for **every** natural `z`, by the actual first/second
projection adapters and the four exhaustive opcode cases. No clean payload,
packed-input premise, boot candidate, or finite test range is assumed. The
focused checks retain raw zero, arbitrary AX parameters and arbitrary raw Nat
inputs. A nonempty shifted program pointer must still be fetched/decremented
according to `EnumPerm.fetch`; this leaf does not prove that runtime operation.

## Independent fresh replay

The durable bundle is `arithmetic-command-wordperm222-peer-replay/`:

| Artifact | SHA256 |
| --- | --- |
| `replay.py` | `775311aa00bb8715b25f10dd91f02aab0e0abba350463462be7a923aae72139f` |
| `inputs.json` | `9814ec8ff6c8f2a4cefd043c1fc34b79772870b75dd72b832304b4b46c35fca4` |
| `RESULT.json` | `dbda996d043f6c48937c1c674e19b5dbaab371b5721e4de520c7df18a9cacfbd` |

The driver was fully read before execution. It independently parsed each
selected source's import header, compared it with the author metadata, checked
dependency order and closure, and verified all 634 retained pre/post pins.
It reused 101 exact current-source custom modules (86 Foundation), 359 cached
custom artifacts, and 37 explicit package/toolchain boundaries including Init.
The package transitive closure is the existing accepted compiler/package
boundary; it was not rebuilt or newly reviewed as a whole.

Both new leaves were compiled sequentially into the new private directory
`/tmp/wordperm222-independent-as36uccd/lib`, using the recorded Lean 4.32.0
executable and `-M6000 -j1 -DElab.async=false`, with a 512 MiB free-disk guard.
Dependency links point to pinned read-only providers. Neither fresh output path
existed or was a symlink; the checks resolved the independently fresh main
object first. No shared cache, accepted source, vendor file, or Git state was
changed. No dependency or Foundation source was compiled.

The independent main replay passed in 5.68 seconds with an empty diagnostic log;
the checks passed in 2.18 seconds. Both object files are byte-identical to the
author's final objects. All nine requested axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. In particular, the use of
choice in the inherited model Cantor projections is reported, not hidden as an
intuitionistic object-language inference rule.

## Development-history distinction

The author's first source SHA256 was
`9d4a1c1af65b0bf0c40547d64a4b7c8c39160a1813e2dbba83c173d9d97fc196`.
That run failed: bounded-branch inequalities and standard/model numeral
identification were not yet discharged. Its snapshot, diagnostics and FAILED
record are copied under `author-failed-*` / `author-run-1793059040016842800.json`.
It is not counted as a successful check. The frozen source above supplies
those proofs explicitly and was the only source independently compiled here.
The independent replay had no failed Lean runs.
