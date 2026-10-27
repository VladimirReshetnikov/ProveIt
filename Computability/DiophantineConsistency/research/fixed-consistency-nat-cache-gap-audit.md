# Fixed consistency target: current-source cache boundary

This is a **read-only dependency and provenance audit**, not a successful
compilation of the fixed consistency comparison. The generic standard-natural
semantics theorem in `FoundationPAHFNatSemantics` has been separately checked.
The proposed fixed comparison remains unexecuted.

The selected route uses the actual Foundation `ZFC.consistent` sentence, its
existing Gödel–Gentzen translation, the repository's arithmetic validator
comparison, and the existing C254 proof-convention comparison with
`SetTheory.BProv SetTheory.ZFCax_s [] SetTheory.Form.fBot`. C254 is used only for
this standard-natural proof-convention comparison. It does not replace the
actual current215/222 machine calibration.

## Reproducible inventory

The complete dependency-ordered source inventory and proposed refresh are in
`../reviews/fixed-consistency-nat-cache-audit/`:

| File | SHA256 |
| --- | --- |
| `inventory.json` | `f39f0858705b7212c6f333482d1234f06012c6bf7b56d71b4d58fe9f8a9e6bbf` |
| `refresh-plan.json` | `9e3911caaadd1c4a1d18162089dc9a9fcc19865dcd2c9dc7b63838d564d6d530` |
| `external-boundaries.json` | `23402a78bac31bb4905d4016fc22940191cf0a3db862104ba16efa15cf030af3` |
| `extra-foundation-trace-auth.json` | `081617899c7901d7d8332fce0cd597f6bfc28344cd97ed5cd269217a61e40534` |
| `private-set-theory-auth.json` | `515bad0219ecb34f9ed937d0a9383e0db1c4061d8df91723e4aa50b68607e1e2` |

At source snapshot `7cfd66cc83de6d0f9185048d06a6bd35e1c49f4a`, the six
inventory roots have 409 custom modules, including 139 Foundation modules,
and 51 direct package/toolchain import names including `Init`. Every selected
source is pinned individually; a later unrelated Git change does not silently
change the selection.

Per-module evidence covers 341 matching source/object providers. The remaining
68 comprise 55 modules for which this search found no matching attested pair,
and 13 with only historical reuse records. The latter records are not promoted
to fresh compilation attestations. These are search-scoped results, not a claim
that no other provider could exist.

The conservative proposed refresh has **73 modules**: the 68 gaps plus five
already compiled clients importing refreshed dependencies:

- `ZFCinPA.NativeInterp`
- `ZFCinPA.NTInterp`
- `ZFCinPA.NativeSchemaSem`
- `ZFCinPA.NativeFixed`
- `ZFCinPA.NativeSchema`

`fresh-order.txt` and `refresh-plan.json` give the complete dependency order,
all 336 reused selections, every source hash, every selected object hash, and
the exact import graph. The plan mechanically checks that **no reused custom
client imports any proposed fresh node**. The accepted generic
`FoundationPAHFNatSemantics` leaf is one additional reused prerequisite, making
410 existing prerequisites before a future fixed-target leaf and checks.
This is a plan only; no one of the 73 sources was executed by this audit.

An earlier provisional inventory had 70 gaps and 98 affected modules. Reading
two different historical record schemas recovered the successful source builds
of `ArithmeticHistoryRecurrence254` and `ModelCodedPredicateTemplate`; this
removed the early recurrence gap and its downstream refresh requirements.
The 68/73 counts above supersede those provisional numbers.

## Foundation and compiler provenance

All 139 Foundation modules have source-matching providers. Ninety-five were
already covered by accepted current HA/arithmetic inventories. For 39 new
central modules, the actual current source and all four `.olean`,
`.olean.server`, `.olean.private`, and `.ir` files match their Lake trace hashes.
The trace compiler is Lean 4.32.0, commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`; the executable SHA256 is
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
Only the already reviewed `FoundationTraceHashes.lean` utility ran, to hash 195
files. It did not build or import a Foundation proof source.

The five remaining modules are `SetTheory.Basic`, `.Basic.Misc`,
`.Basic.Axioms`, `.Basic.Model`, and `.Z`. Their current sources, saved source
snapshots, historical successful source commands, captured outputs, compiler,
and `.olean` hashes match executed private 4.32 records. `Model`, `Basic`, and
`Z` have all four artifacts recorded before their historical audit. For `Misc`
and `Axioms`, the `.olean` hashes are historical, while the six companion hashes
were recorded later and checked unchanged now. The manifest explicitly retains
that distinction; it does not invent historical companion attestations.

The plan pins all existing companions it finds. Many legacy custom modules
have only an `.olean`; their absent companions are listed rather than copied
from another provider. This audit does not claim a successful import of the
combined 410-module environment. The 51 direct package boundaries are pinned;
their transitive Mathlib/Aesop/toolchain closures remain the existing accepted
4.32 package boundary, not a new package replay.

The narrower Encoder222 request is separately covered by
`encoder222-foundation22-auth.json` (SHA256
`6279f7df8780b39d1b25701df2ddee960cdca8cc1e8950fa51d7fb0d7405094d`):
20 of the new central bundles plus `Misc` and `Axioms`, with the same provenance
limits. Its preserved original request and corrected 151-custom-module request
are both pinned. Its three extra local ZFCinPA clients are a separate check.

## Important endpoint gap

The current sources of these three modules exist and were inspected, but this
inventory has **no matching executed source/object pair** for them:

| Module | Current source SHA256 |
| --- | --- |
| `ZFCinPA.R2Native` | `5dede1cf75df4ae1d9309cd24f6febe3573557fadbd037aeada97988260f68c4` |
| `ZFCinPA.LSchema` | `c68dbfb6e9b152ab71654de3a2b2cf3559ebe1f8e616edabd12e24209ea568f2` |
| `ZFCinPA.ValidatorConsistencyEquivalence` | `e0502e78a7c1a4a8c6d3f242279ae557ce91678dfd9cb52aa628bf38c0fbd242` |

In particular, `/tmp/zfc-r2-native/freeze.json` explicitly records
`SOURCE_AUDIT_DIRECT_GUARD_FROZEN_UNEXECUTED`, and its boundary records
`FROZEN_BOUNDARY_FOR_UNEXECUTED_DIRECT_GUARD`. The earlier upstream review was a
source/API review, not an executed build of these endpoints. Status documents
must therefore describe this portion as **source-only, pending current-source
validation**, until a new complete scoped replay actually passes.

No historical checker was executed here. The inventory scripts only read and
hash metadata, sources, snapshots and objects, and write this new audit packet.
Development encountered heterogeneous JSON fields (list, map or count); those
parser failures occurred before any theorem build, were corrected explicitly,
and are not proof failures or successful replays. The final read-only scripts
complete successfully. No accepted source, vendor file, shared cache or Git
state was changed by this packet.

Even a successful future fixed Nat comparison will establish only the concrete
sentence's **standard-natural meaning**. It will not by itself prove HA
normalization to an independent untranslated proof checker, an HA derivation
of the current equation's equivalence, or the missing actual215 internal PA
calibration. The existing finite-theory HA transfer retains its source PA proof
premise until that proof is genuinely supplied.
