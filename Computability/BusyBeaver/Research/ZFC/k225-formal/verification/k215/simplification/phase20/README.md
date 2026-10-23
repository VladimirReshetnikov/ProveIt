# Phase20: share AX words and the 219 macro contracts

**The Lean check, independent result review and independent evidence capture review pass.**
This continues [phase19](../phase19/README.md) at
`a3f35bef3cfb9bc24c98fd48567f3229dba69052`. The machine remains at 215 states and the
endpoint statements are unchanged. The internal PA endpoint and a minimum-state theorem
remain open.

[`AXWord`](../../../../../../../Lean/BusyBeaver/ZFC/AXWord.lean) composes the native macro contracts once, including the two-node literal read.
The 222, Perm and Dom routines supply their eight-atom prefixes and share a 148-atom
suffix. Each literal program retains its own finite word check and exact `ax_eval`
statement. The 219 AX facade transfers the 222 run contract through the existing
equality-test equivalence. These replace the generated per-node AX proof chains.

The three 219 macro modules share `L2K`'s state and pure facts, and forward 55
program-specific run contracts through `Dag219Bisim`. Their typed macro arguments and
results are preserved. The old nominal identity of `L2Q.AS` and its qualified generated
constructor/projection namespace lie outside the preserved contract. Record construction,
updates and the maintained root callers are included in the selected Lean check.

The unused 219 `while_AS`, `inc_AS` and ten local equality helpers are retired. The
222/219 generated AX internals are also retired while `f236`, `l236`, `c236` and
`ax_eval` remain. Perm and Dom's helper definitions (`pushA`, `popA`, `gateF`, `AXAtom`
and the word machinery) move to `AXWord`; their old qualified helper namespaces are
outside the preserved facade API. The unused local `l457` wrappers are removed.
Source censuses cover all 32,415 Lean files in the four maintained roots and fifteen
accepted typed clients. They find no maintained external callers of the retired or
moved names; they make no outside-repository API claim.

Seven Lean modules are replaced and one common module is added: **3,528 → 469 lines**,
removing **3,059 lines / 417,103 bytes**. The three obsolete writers
[`generate_l2axioms222.py`](retired/generate_l2axioms222.py),
[`generate_l2q219.py`](retired/generate_l2q219.py) and
[`generate_l2axiomsdom.py`](retired/generate_l2axiomsdom.py) are retired with their
original bytes preserved. They account for another 704 lines / 30,370 bytes, for
**3,763 lines / 447,473 bytes** removed from active maintenance. No supplied generator
was executed.

These are savings across the selected compatibility sources. The primary 215 endpoint
previously used a compact Perm AX proof; sharing its proof adds the common module.
Its closure grows from 178 to **179 modules**, and from 1,765,109 to **1,768,653 source
bytes** (+3,544 bytes). The large 219/222 AX scaffolds were outside that primary closure.
See the [exact source measures](integration/source-metrics.json) for the exact source measures.

The frozen check covers **227 providers**: 212 project modules and fifteen unchanged
typed clients. Fourteen providers compile fresh and 213 reuse the accepted phase19
source/object/dependency/log bindings. Both endpoint audits compile fresh. The fresh
providers and audits have zero warnings; sixteen expected warning occurrences are
inherited from the accepted baseline. The source-forward and site certificate batches
reuse their established checked identities. This verifies the selected 215 endpoint and
compatibility facades; it does not establish new endpoint results for other machine variants.

Earlier compiler attempts and their record-syntax, callback-binder and unused-simp-argument
repairs are retained. The accepted run uses the final source revision with unchanged proof
policy and resource limits. Its result is
`a334d6f473529c70bfc07dc16ad49bf2f7f0902a3ed39f6f30734e8886700e0d`.
The [independent actual readback](lean/result-review.json) checks all source, object,
dependency, log and toolchain bindings, including 196 adjacent raw provider records.
Thirty-one inherited providers retain the accepted aggregate boundary for missing
original raw records; every fresh check has an explicit exit-zero raw receipt.
The [independent capture review](integration/capture-peer/actual-review.json) verifies
all 484 archive blobs, 1,146 logical entries, 1,139 source aliases and 926 raw evidence
rows, including all three rejected histories. No compiled object is shipped.

The [Lean evidence](lean/README.md) records the accepted check and its exact inputs.
Eleven phase19 Lean evidence leaf files remain exact historical boundaries. Earlier
compiler history, raw logs and recorded source hashes retain their original meanings.
