# Annotated row lookup simplification validation

Source commit `d3baf45019f6d1145a42a935eb1808f3b0ee5cc3` and parent `1eb30cb8d1146f9dfbb38db79a3fab1d76a84ed9` match both tested target snapshots. Two private lookup_after helpers are replaced at their sole uses with direct simplification. The change removes 12 net Lean lines without adding imports or changing existing public theorem statements. The old helpers came from commits `69b1d0693c1` and `12a8d2671f8`; no Claude coauthor is asserted.

Target source SHA-256 (parent / commit):

- `AnnotatedRename`: `b2b614db72b193f2a4b4ee14132757ff8f98d82963694802efb3e812281b0df1` / `aabe85bdc2e0c955705bb1de034e3907989c92d3c598cad6af02d3402c441966`.
- `AnnotatedBound`: `cfecd9e36dcc48b17285b86737714c9ce54db7457e382fc154fb9208230b5c97` / `92d1f874fff8b5a0ffbc1b31ee7a077bf00af435e72e70ec0e02e49e2a11ae4f`.

Both paired source-ordered lanes pass all nine modules, plus the standalone AnnotatedBound check. The seven unchanged module objects and the expected check output match byte-for-byte; the two target objects differ. Module build logs are empty, and check logs contain matching expected `#print axioms` output without warnings.

| Module | Baseline object SHA-256 | Final object SHA-256 |
|---|---|---|
| `AnnotatedRename` | `b20496d005a7652c02105a3d1abbe7f20695a5ed8866fae1c0049e2ab41dc684` | `382df0252eadde950bde5cea3a70f6e25c3005bdc6682016018a4eaf732f2058` |
| `AnnotatedRenameCode` | `4924a49f2dc9a1d2ffb5f557ee42372d2298c0a3d50bf618ccf5f0bbc16549ce` | `4924a49f2dc9a1d2ffb5f557ee42372d2298c0a3d50bf618ccf5f0bbc16549ce` |
| `AnnotatedRenameArithmetic` | `bf29cdd77c792aceaeb7b3f13eb1d9cdf559cd5c9450c65057c242828d37b277` | `bf29cdd77c792aceaeb7b3f13eb1d9cdf559cd5c9450c65057c242828d37b277` |
| `AnnotatedRenameLocal` | `69e502337add2f5f0973423a91cc03e6160ea3c9ce50ac7ae0072ec0358cdb1d` | `69e502337add2f5f0973423a91cc03e6160ea3c9ce50ac7ae0072ec0358cdb1d` |
| `AnnotatedRenameLocalPR` | `c2e2905752863fc8ab94403d00fafd0f6592fb7fff7062a364d6be44138eb3e5` | `c2e2905752863fc8ab94403d00fafd0f6592fb7fff7062a364d6be44138eb3e5` |
| `AnnotatedRenameScan` | `108d73f63d3483af362f36522e488a6000eeebf16172892972ac7f718ebc8707` | `108d73f63d3483af362f36522e488a6000eeebf16172892972ac7f718ebc8707` |
| `AnnotatedClosure` | `cc1d25d027b1aa30483dbb170cde4c8d3ed277c9d969dcba0a273eecfbe37205` | `cc1d25d027b1aa30483dbb170cde4c8d3ed277c9d969dcba0a273eecfbe37205` |
| `AnnotatedBound` | `75a6f41e63a9c9f880074ae5ac0b91d1352f5e97a145ec55ee0a1da4d5954013` | `8d6f64470748a555815304a33d5d2bae82f178737c5ef5e61e73b8610067f9bc` |
| `AnnotatedBoundLocal` | `e6725aa9fabdd4deb060ac9ee08d1f26f96a252fecbd88f68632a6194c5e97ac` | `e6725aa9fabdd4deb060ac9ee08d1f26f96a252fecbd88f68632a6194c5e97ac` |

Eight probes pin all nine phase objects. The 398 common namespace declaration names, printed types and axioms, and sampled global simp/instance registrations match. The only removed names are the two private `lookup_after` helpers and their two private proof helpers. No new names appear. A search covering 90,633 tracked and nonignored untracked Lean/Python paths found no references to the removed fully-qualified names. Printed reports do not establish proof-body or all persistent-extension equality.

Two external direct project inputs have source-current producer associations:
- `AnnotatedCodeArithmetic`: object `78a1154dcc2839802487d9cc39b09a8832b2edace38fd2cd7d24d0700783b0e5`, source `f83ffce78772a76babae394f8b827d2bcdcc77b6776c20b749aaf216b4f32364`, producer `/tmp/annotated-bound-witness/directverify-records.json`.
- `NatIterate`: object `a2b3584a30113ae1887a0a67198cc6f51f809c98f3acd0c26f5e6ab3ba48e2ed`, source `c52148b71e86cc8f8713889f92bc321160292cc9ab1b6237ae417fc8f847fb2a`, producer `/tmp/annotated-bound-witness/common-prior-records.json`.

The final client input source-path samples for the two changed targets reflect the pre-adoption workspace baseline; target build rows separately link actual phase objects to phase snapshots. The umbrella and wider project/Foundation/Mathlib dependency closure were unbuilt or cached. No complete source-current transitive build is claimed. The independent review checked first-path resolution, all paired builds and probes, provider associations, reference search and postcommit snapshots.

No raw logs or compiled objects are included. The following temporary external evidence may disappear; hashes identify the checked files:

- `/dev/shm/annotated-lookup-simp-133/baseline-records.json`: `a37cf18d39658317ae457caec9093fbee279ee9a3cfa3004f1af2df699b1dc59`.
- `/dev/shm/annotated-lookup-simp-133/final-records.json`: `f25602c083796a7fb9ff72d2130750f523006021a0dcae51c1e0a9d57aacf3e4`.
- `/dev/shm/annotated-lookup-simp-133/baseline-check-record.json`: `3ffaf5b9c87efede5e04d8b48057ac492f46afa8b48ccf780b6caabab8c4cc17`.
- `/dev/shm/annotated-lookup-simp-133/final-check-record.json`: `1cdc7225722787c5901c8a08827be89a58ce68f50a5805525eb7ada721571893`.
- `/dev/shm/annotated-lookup-simp-133/probe-records.json`: `cf7467efa304f462335be8a3ff15f59f3b85850ae0cae89b6633365ae2b083ad`.
- `/dev/shm/annotated-lookup-simp-133/reference-search.json`: `96126397e5df44fd7719110207e758504785b63cfcc303ab72ec6a68b3a6a837`.
- `/dev/shm/annotated-lookup-simp-133/audit.py`: `08bed8da6956fa62a89ff2c71688739b6ebc93552375d859c3e6e1b46bd88f44`.
- `/dev/shm/annotated-lookup-simp-133/audit.log`: `0c63a9aca5c88d24cd1b5d25b1b6997743931f55c0ab9501e1ed955562035b10`.
- `/tmp/annotated-lookup-simp-132-review.txt`: `74bed2739884ccc6490ff26f6ed8b2f8576c859ffb7751d97c70531d6496bb23`.
- `/tmp/annotated-lookup-simp-132-peer.py`: `0646ff1a71d98ef5c8417af1484a6a84af776aaae771f1e9f3a6f12a12170c8a`.
- `/tmp/annotated-lookup-simp-132-peer.log`: `49d99be3e815d75aa4ac117f756c029ea2f732d4b3628694e9d7fdb39ef1fcc8`.

Full replay requires those external records, compiled dependencies and the build environment. Timings were single shared-load observations, not a benchmark.
