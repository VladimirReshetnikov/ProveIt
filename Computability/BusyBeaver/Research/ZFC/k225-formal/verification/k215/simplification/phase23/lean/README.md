# Phase23 Lean evidence

**Kernel, independent actual readback, capture and independent capture review pass.**
The selected run checks **230 providers**: 215 project modules and fifteen unchanged
typed clients. **199 compile fresh**, 31 reuse exact phase22 bindings, and two
endpoint audits compile fresh. Fourteen clients and all **25 site/Fwd batches**
are fresh. The run takes **2,066.82 seconds**, an observed duration rather than
a comparative speedup. All 230 provider logs and both audits have **zero warnings**.
All 93 client, five WFTheory and ten endpoint-audit profiles remain exact.

The [actual readback](result-review.json) checks **1,259 owner inputs**, 146 present
pins and sixteen absences. Adjacent raw provider records: **218 present / twelve
inherited absences**. Missing inherited records keep their historical aggregate
boundary; no fresh invocation borrows it and no receipt is fabricated.
No additional focused helper audit is included this phase.

The 33 maintained files shrink from 7,342 to **7,099 lines** and 340,391 to
**327,375 bytes**: **243 lines / 13,016 bytes removed**, including new Core modules
and retained facades. Separately, the primary closure changes from 179 modules /
1,768,101 bytes to **172 / 1,728,487**. These overlapping measures must not be added.
See the [source review](../source-review.md) and [compatibility notes](../compatibility.md)
for forty API retirements, three stronger types and the one-Separation/one-image
attempt construction. Machine and endpoint statements are unchanged.

The failed full-v1 prefix and failed math-v1 diagnostic remain history. Math-v2
passes 107 fresh modules as a diagnostic only, not a full-run reuse basis.
Its three stale informational size fields are disclosed in the
[source peer](../integration/source-peer.json); exact source hashes bind the final
bytes and final full-plan counts are correct. That source receipt retains its
original pre-full-run status; later terminal receipts establish acceptance.

[Terminal result](result.json) SHA-256:
`684d93cbb3b49a25587ca2177d49789ff8e6dad0c06e5f9823803d665304cffe`.
[Actual readback](result-review.json) SHA-256:
`edf3adfd15948e9dc74f835675acf39ecab956053f4c9b3704c90bbf224b04ff`.
The deterministic [capture](capture.json) passes for **928 blobs / 2,078 logical
entries / 2,074 source aliases / 1,089 raw evidence rows**. Archive: **3,389,911 bytes**,
SHA-256 `573012336488f152e622798d08f7782ea90310b6dc994864c51c1315f9001dd6`.
[Index](index.json) SHA-256: `cf1994f345795d5cffc259acce1aa03b031f38ad695c1d53fe2a3d2bbe7d0038`.
[Capture receipt](capture.json) SHA-256: `b800f5a8bfd7b8652981a405e5978f64a3eb23195b64c404a739de7e8ba0c855`.
[Configuration](capture-config.json) SHA-256: `dec64746ffa236bd5f9388317efaf9950cf9a8d7d10caa2ca60cea2a4fccc8c8`.
[Independent capture review](../integration/capture-review.json) SHA-256:
`8edb3611f7498756d8dab6f0762067e5152702190c5ac048d442a33dc1e1d290`.

A prior reader failed on a duplicate canonical-alias assumption; its
[stderr](../integration/reader-history/failed-review.stderr) remains history.
Reviewed [version4](../integration/review_capture.py), SHA-256
`da06f2f04ce9a2e3e87cadce8da69b8115230f90501fa9f8555572bc8729eb2a`, checks live canonical digests, archived workspace digests and
historical labels for all 33 overlays. The archive, config and index are unchanged.

Use the index to resolve logical entries and source aliases to archive blobs.
Historical absolute paths are labels. Inspect bytes without extraction or code
execution; executable proof objects are not shipped. Three wrappers require the
captured config and adapter (five phase assets), plus three phase22 base helpers:
**eight runtime assets**, not a standalone portable `check.py`. Phase22's **eleven
exact external Lean evidence leaf files remain immutable**. The
[uncompiled lead](../leads/README.md) is separate. Internal PA and minimum-state
claims remain open; see the [checkpoint](../README.md).
