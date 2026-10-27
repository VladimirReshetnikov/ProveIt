# Author receipt: ordinary source to current Carrier65

Author implementation and full source/driver self-review, 26 October 2026.
This is not an independent peer review. Only the two new Lean files and
this new replay/receipt were added. No accepted source, shared object,
display or central documentation was changed, and no Git command was run.

## Proved scope

`NativeOrdinarySourceConstruction.source_constructs_carrier65` accepts
an arbitrary strictly positive natural 31-coordinate zero of the literal
`SplitCertificate59.sourceRows`, a finite `NativeSourceMask.Interface`,
and the low mask residue `MC % 4 = 2`. It produces a strictly positive
14-coordinate zero of `Carrier65.polynomial` with the identical J, F,
alpha, **old z**, and w. In particular, it does not require an ordinary
private multiplier to be divisible by the discriminant, a supplied
canonical seed, a Carrier65 zero, or any additional rank premise.

The new ring identity binds `NativeRankVariation.windowRank` to the exact
ordinary `nativeRank`. Source positivity justifies its natural conversion.
`sourceData` copies all six scalar fields, including C, and proves every
field of `NativePositiveSourceConstruction.Data`: positivity, both balances,
the forced binary product, the old-z transport equation and the rank.
`source_native_window` supplies the original N, exponent d*N and population
identity; `source_rank_mod_four` supplies the same rank's residue. The
accepted population construction then **rebuilds private Pell witnesses**
using these data. It does not silently retain arbitrary supplied f or i.

At the literal current ports, `current_source_iff_positive_zero` proves
existence equivalence with `CurrentPolynomialWindow2011.polynomial`.
The forward direction applies the all-positive source theorem. The reverse
direction uses the actual polynomial zero's proved canonical restoration
and `Carrier66Source.sourceNat`; it makes no claim that arbitrary ordinary
private source witnesses are canonical. Both directions use the identical
once-shifted four current ports.

`current_source_iff_not_conZFC` and `no_current_source_iff_conZFC` compose
that existence equivalence with the accepted external endpoint for the
actual `DiophantineConsistency.ConZFC`. They are external Lean results,
not object-language HA/PA/ZFC proofs. No equation metric, historical
13/88/51 or 12/96/70 transfer, shifted-z adapter, adaptive-carrier
completeness, or free-J transfer is claimed. Those remain separate steps
in the [read-only transfer audit](../research/ordinary-low-degree-current2011-transfer-audit.md).

## Frozen source and objects

| Artifact | SHA-256 |
| --- | --- |
| Main, 156 lines | `95e7a8cd4d2dd8f64554cbd9273d96e9629d12583f111cc0b89bee325712838b` |
| Checks, 53 lines | `a2a2e425a8953ec5aa537f8abe673f179c82e945508e2889993d6c2f4efc1493` |
| Main object | `67c28fd51812ecf959df72aaa46cbdaa243ea629c860ffd57fe5808fe6fc49d8` |
| Checks object | `f824a076b610b1f5f6b1d2f625dc1bcfe4512ea80ea00b3eab25dc257e6b1e8a` |
| Final driver | `b159507bbd334936390727f855826104a9840b7a509346fb82013ebd7b38d504` |
| Final input manifest | `5a5833081c2167e5b7ad8b150fff7306f8a6cdfddf678c2c4f8e239a0bceee13` |
| Final run state | `aa03e73014347d87122c4cf1582abafdfcc27ebb06c7082ebfaa202f4cc32316` |

The main and checks are in `Lean/DiophantineConsistency/`. Final private
objects are in `/tmp/native-ordinary-source-onjq2zfu/lib/DiophantineConsistency/`.
The complete [durable replay metadata](native-ordinary-source-construction-replay.json),
SHA-256 `c73617b3fd69519347f1b329b2167d2be394ec974ee17bbe7a540417c5d65d2b`,
includes the driver text, both attempts' source snapshots and input
inventories, logs, timings, commands, all final object pins and the
pre-execution authentication failure.

## Authenticated bounded replay

The exact import DAG selects **364 cached custom modules** from the
accepted current provider `/tmp/thirteen-scaled-syzygy-native-g4p5s1dn`.
Each selected source, current source and primary object is hash checked;
the two source versions agree. In the inherited provider accounting,
107 were parent-fresh and 257 were parent-authenticated reuse. All 364
are reused here; only the two new leaves are freshly compiled.

The actual external import boundary contains **64 module names**,
including implicit `Init`. Every such source and primary object, and each
present private/server companion, matches prior pinned evidence. The
root narrow-native plan provides most pins; the accepted
`foundation-ha-zfc-validator-root-replay/ROOT.json` supplies the three
additional Mathlib boundaries (`Data.Fintype.Sum`, `Data.Nat.Digits.Defs`,
`Order.Interval.Finset.Nat`). The complete 988 input pins are checked
before and after the run and again at freeze. This is source-authenticated
reuse plus a two-leaf replay, not a new transitive Mathlib/toolchain replay
or a new whole native closure build. No Foundation module is built.

LEAN_PATH contains the private linked custom overlay and the ten explicit
package/toolchain roots recorded in the manifest, with no project shared
object directory. Commands use the pinned Lean 4.32 compiler with
`-M6000 -j1 -DElab.async=false`; both new sources were read before execution.

- Main: exit 0, 4.030 seconds, peak RSS 3,354,260 KiB, empty log.
- Checks: exit 0, 3.337 seconds, peak RSS 3,340,596 KiB.
- Twelve axiom reports, each exactly the standard `propext`,
  `Classical.choice`, and `Quot.sound`; no `sorryAx` or new axiom.

An initial authentication-only attempt stopped before Lean because the
narrow provider did not list all external boundary imports. Accepted
prior pins resolved the gap; no current-only hash was substituted. The
first actual main attempt then failed because the generic rank expression
inferred Nat from its first argument. Explicit Int casts in the main
statement and its focused check fixed that elaboration issue. The failed
source/log/state are preserved, and the complete pair was then rerun.

Compilation was held when disk space approached the 512 MiB reserve.
Root recovered space by byte-identical hardlink deduplication of its own
completed caches, preserving every path and hash. No active output or
source was touched. The replay embeds that recovery receipt; free space
after saving the durable metadata was 548,814,848 bytes, above the reserve.

The focused checks cover exact scalar fields, the unrestricted positive
source theorem, the same rank and transport equation, both actual current
existence maps, and the external consistency endpoint. No shifted-z or
unauthenticated historical source module was compiled.
