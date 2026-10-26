# Independent read-only review: actual Nat C222 checker

Reviewer: `/root/complemented47_review`, 26 October 2026.
Status: PASS within the external Nat checker scope; no finding or requested
source change. No independent Lean compilation was run for this review.

I read the entire new main/check pair (132/51 lines), the entire
`Code254Proof.lean` source including its parser and roundtrip proof, the
actual `KCode222` constructors, and the shared numerical formula definitions.
I read the author receipt and preparation/compiler/receipt drivers as text,
then independently checked the recorded source/object/log provenance.

## Semantics and exact reuse boundary

`conclusion222` is genuinely new recursive semantics on the old raw tree.
The raw node `.r7` still quotes to base12 tag9, but now denotes exactly
`KCode222.growG`, including its added universal binder `wel a b`.
The `.bundle` node denotes exactly the helper-free
`KCode222.bundle222`. Generalization recursively uses the **new** child
conclusion. All other leaves agree with the actual corresponding C222 rule.

`valid222` recursively validates both MP subtrees and compares the new
major conclusion with `wim (conclusion222 minor) output`. Neither the old
MP conclusion nor the old `RawProof.valid` is reused. Generalization checks
its child. The only bundle conditions are `c != a` and `c != b`; there is
no extra `a != b` or nonzero-label condition.

The new `sound` proof inducts over raw trees and applies the actual C222
constructor in every case. In the MP branch, the exact checked major-formula
equality transports the recursively obtained C222 proof before applying MP.
`rawProof_exists` inducts over an actual C222 derivation and constructs an
existential finite raw tree inside `Prop`; it does not inspect a proposition
to define a selected executable tree. Both changed axiom cases use their
actual new conclusions. No old C254 semantic soundness or completeness
theorem is invoked.

The reused `quote`, `height`, `height_le_quote`, `decodeFuel`, and
`decode_quote` are syntactic. The roundtrip is proved for **every** raw tree,
including invalid proofs, so changing the interpretation of two nodes does
not invalidate it. The parser uses depth fuel and returns `none` on zero,
exhausted fuel, or malformed truth payloads. `check222` supplies `code+1`
fuel; quoted trees have height at most their quotation, ensuring completeness.
After parsing, the checker still separately validates the new tree and
compares its new conclusion to the requested formula code.

The resulting theorem is exactly

```text
KCode222.C222 n ↔ ∃ code : Nat, check222 code n = true.
```

It handles every natural input. Proof code0 is rejected, while proof code1
is the quoted truth tree with formula code0. Formula false code1 remains a
different notion. Focused checks cover the changed tag9 and bundle semantics,
both MP child conditions, the permitted bundle `(a,b,c)=(1,1,0)`, and rejection
of each forbidden bundle-label collision.

This is an external numerical coding theorem. It does not establish an
internal IΣ1/PA represented C222 history, internal seed validity, a C222-to254
refutation translation, the actual counter4/215-machine runtime linkage,
or the requested HA equation equivalence. The author receipt correctly
retains those remaining obligations.

## Exact pins and provenance

Sources under `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`:

| File | SHA-256 |
|---|---|
| `Code222Proof.lean` | `7e91fc3c3fca914db3b9063003e273dfa49f773c20366f61b23afe79ac48d1f5` |
| `Code222ProofChecks.lean` | `d5b3af67bdb9a338c5252e6863d8b5580d99a5ed66b9c478fd0c157ad3e35206` |
| `Code254Proof.lean` | `7bb8daf0f1c0965d22f2f16bbb1898d60cfb79f9a6feabe8ab38b3f69b3bc6d1` |
| `KCode222.lean` | `fbc4fef6e479b6bc5bc83bcfafa73fb1befdc1b1d02b605da68ecf691f641eb3` |
| `Code254.lean` | `efffed3d6c96bb073d444c35352361347b6e2415b8c9e95b8bc860ecda3eb05a` |

Author receipt SHA-256:
`0f9926f94b07f569925649cc9a60af004f848215e7dfba3bef341e441e201fcb`.
Complete replay receipt SHA-256:
`a854e8bac4a703a5e801483943af53904e79548216b9a0863f31d5c5805cb5e9`.

I independently rehashed all13 selected custom source/object pairs, their
one explicit `Init` boundary object, compiler, Lake manifest, input inventory,
three drivers, both final source snapshots/objects/logs/timings, and both
recorded development-run manifests. Every hash matched. I checked all
selected source import lists and their closure relative to the recorded
boundary, and matched each reused source/object pair to the frozen growG
parent receipt. There are no Foundation modules in this selected closure.
This is provenance authentication of the author's two-leaf replay over
accepted caches, not an independent or broader closure compilation.

The final two commands used private overlay
`/tmp/code222-controller-mhs20gs0/lib`, Lean4.32,
`-M6000 -j1 -DElab.async=false`; both exited0. The main log is empty.
I read all nine focused axiom reports: five use only `propext`, and four use
only `propext`, `Classical.choice`, `Quot.sound`. The final fresh object
hashes are `c7d6713935acd3a914bb1ce659340c6fe11034f383850177fa414a6c4cdc1b0d`
and `79f8d98dbdd18399b1848232f16601e8117e9069c9200a634a2b778f14a7989c`.

I compared the retained failed-main snapshot with the final source: the
only change expands the `accept_bundle` corollary's Boolean gate proof.
No definition, statement, semantic induction, or parser premise changed.
The unsuccessful simplifier attempt is accurately disclosed.

I authored the earlier C222 internalization audit and some upstream native
and arithmetic215 cache-provenance work, and reviewed growG/seed templates.
I did not author this checker, the original raw-tree/parser packet, or its
proofs. This independent source/math and provenance review made no changes
to accepted source files, shared objects, central documentation, or Git.
