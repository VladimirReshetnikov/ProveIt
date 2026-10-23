# Phase23: generic Core proofs and native Replacement

**The serial Lean kernel check, independent actual readback, evidence capture
and independent capture review pass.** This continues the published
[phase22 checkpoint](../phase22/README.md) at
`017861249e7da624c007e0dd6d170e32433be549`. The literal 215-state machine and
its halting/nonhalting endpoint statements are unchanged.

The 33-source change combines Claude's generic semantic split and unused-theorem
cleanup with native Replacement, direct attempt extension and scoped warning fixes:

- Four Core modules hold the generic finite-set, singleton-infinity,
  inductive-attempt and well-founded-part proofs; old quotient facades remain.
- `KQ1Replacement` uses the existing formula-indexed quotient Collection theorem
  with the exact domain guard and slot renaming. Six obsolete raw helpers retire;
  the file shrinks from 142 to 59 lines and keeps three declarations.
- Direct attempt extension needs one agreement Separation cut and one functional
  image. A base attempt places the initial value in the image; each recorded
  witness extends directly at the successor. Five existence helpers retire and
  `closure_of_instances` loses its redundant `hEx` premise.
- Constructive semantic congruence shortens the surviving formula proofs. Two
  Gam signatures drop four unused arguments, four direct callers change, four
  internal lambda binders become anonymous and one unused simp argument is removed.

Claude's Core split `474c62c24e1bef804a3af7a7fe5ee22fa7662571` and 29-theorem
cleanup `773e57b0987ba0d57e45b32a59b59d5f043f457f` retain attribution through
`-x` cherry-picks `494e85f33ce1c2ac1e65f4832be03d451b1f8c37` and
`858e43c42de48a6d78af57460d5ef5d75e068691`. The native argument adapts the
batch219 consolidation-plan proposal at `56b37bde8b064d852154ad8478d58ec9ab5375d6`.
Phase22's reviewed premise/caller cleanup is preserved.

## Two source measures

| Scope | Before | Accepted candidate | Reduction |
|---|---:|---:|---:|
| All 33 changed/new maintained files, physical lines | 7,342 | 7,099 | 243 |
| All 33 changed/new maintained files, source bytes | 340,391 | 327,375 | 13,016 |
| Primary K215 endpoint, project modules | 179 | 172 | 7 |
| Primary K215 endpoint, selected source bytes | 1,768,101 | 1,728,487 | 39,614 |

The maintained measure includes every new Core file and retained facade. Modules
leaving the primary closure remain maintained and checked for compatibility.
The selected-import reduction is not the whole-maintained saving; the two measures
must not be added. No module or producer is newly retired. The
[source review](source-review.md) gives all 33 file rows; the
[compatibility notes](compatibility.md) identify forty declaration retirements
and three stronger theorem types.

## Accepted evidence and retained histories

The selected run takes **2,066.82 seconds** and checks **230 providers**:
215 project modules and fifteen unchanged typed clients. **199 compile fresh**,
31 reuse exact phase22 bindings, and both endpoint audits compile fresh.
Fourteen clients and all **25 site/source-forward batches** rebuild through source
transitivity. All 230 provider logs and both audits have **zero warnings**.
All 93 client, five WFTheory and ten endpoint-audit reports retain exact profiles.

The [actual readback](lean/result-review.json) checks **1,259 owner inputs**,
146 present pins and sixteen absences, with 218 adjacent raw provider records and
twelve disclosed inherited absences. No record is fabricated. The
[terminal result](lean/result.json) has SHA-256
`684d93cbb3b49a25587ca2177d49789ff8e6dad0c06e5f9823803d665304cffe`;
the actual readback has SHA-256
`edf3adfd15948e9dc74f835675acf39ecab956053f4c9b3704c90bbf224b04ff`.

The deterministic [capture](lean/capture.json) contains **928 blobs, 2,078 logical
entries, 2,074 source aliases and 1,089 raw evidence rows**. Its archive is
**3,389,911 bytes**, SHA-256
`573012336488f152e622798d08f7782ea90310b6dc994864c51c1315f9001dd6`.
The [independent capture review](integration/capture-review.json) passes against
the unchanged archive, configuration and index. Phase22's eleven exact external
Lean evidence leaf files remain immutable; executable proof objects are not shipped.

The first full prefix and first focused diagnostic remain failures. The repaired
107-module mathematical diagnostic passes but is not an accepted reuse basis.
The final full run establishes acceptance. A separate capture-reader failure
assumed duplicate canonical-path aliases; reviewed v4 instead checks each live
canonical digest, archived workspace digest and historical source label for all
33 overlays. Its [failed stderr](integration/reader-history/failed-review.stderr)
remains history; archive, config and index did not change for that reader repair.

The [final source peer](integration/source-peer.json) preserves its original
pre-full-run status and source conclusions. Source-spec/precheck status labels
also remain historical; the terminal results and capture reviews establish this
accepted checkpoint. See the [Lean evidence](lean/README.md) for receipt hashes,
runtime assets and the diagnostic metadata limit.

The [next control lead](leads/README.md) is explicitly uncompiled and outside this
production-source check. The internally encoded PA endpoint and minimum-state
theorem remain open.

[Phase24](../phase24/README.md) passes kernel, actual readback, capture and independent capture review
for 230 providers (121 fresh / 109 phase23 reuses) and two fresh endpoint audits.
Thirteen sources remove 175 lines / 8,435 bytes; the primary stays at 172 modules.
New static batch219 proposal reviews remain separate from these checked sources.
