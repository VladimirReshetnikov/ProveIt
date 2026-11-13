# Failed external-checker author extension: missing parent guard

The planned 35-module single-overlay build is a metatheoretic comparison of
Foundation's selected standard-natural consistency sentence with the
repository's separately encoded annotated primitive-recursive refutation
checker. It is not an internal iPRA checker-comparison theorem. Its manifest
was SHA-256 `eea1923b96112722f8e2a9151cc870250a5b694bd95d772525fabe8127adcb57`.

The actual outer tool session **89111** exited 1; the saved wrapper separately
records child exit 1 and a minimum observed free space of 7,425,544,192 bytes,
so its 4 GiB sampled reserve was not triggered. The runner compiled
`AnnotatedProofChecker` and `AnnotatedProofCode`, then stopped before the
next module with

```text
ValueError: ('external absent from parent audit',
 '/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Mathlib/Computability/Primrec/Basic.olean')
```

The result state is `FAILED`; it is neither an accepted comparison proof nor
a peer replay. The guard requires each directly imported external object and
its companions to appear in the pinned parent guard inventory. A file existing
at that path is insufficient. The source snapshot, two output logs, runner,
wrapper, complete process log, failed state and both exit observations are
preserved in this packet. Binary outputs remain in
`/tmp/ipra-selected-external-comparison-author-20261101/lib` while it exists.

The object resolves into the inherited mathlib checkout, whose recorded
revision agrees with the recovery snapshot's mathlib revision. This is a
checkout observation, not proof that the cached object and its transitive
ancestors were compiled together with the pinned parent. An additional hash
of that object alone would not establish compatible source/object ancestry.
No old or newly rebuilt package object has been substituted into the parent.
The missing provenance must be addressed coherently before retrying.
