# Selector sum positivity validation

Source commit `b82c51d3da28270e444306359cef7c38a2f4d6d7`, parent `1c7fba5d04e70299abb347a8fd2e4adce357e620`. The changed `NativeSelectorClause54.lean` source has SHA-256 `c9318b06362ea9f34fd4637435a4df0694e1f772981aadf95079f189c6d3a465` in the parent and `717c93b917066b1343d92ed953a35252b5f786dedf3cadab94dc1e9f2040870b` in the commit; each matches its tested source snapshot. `Finset.sum_pos_iff` derives a nonzero selector directly from the sum being one, replacing an indirect zero-sum contradiction. The proof removes three net lines and preserves existing imports, definitions, assumptions and theorem statements. The old proof was introduced in `12a8d2671f8`; no Claude coauthor is asserted.

Baseline and final `NativeSelectorClause54` builds pass, both originally and in a replay with a separately rebuilt, current-source `NativeLocalCoefficients54` provider. The respective baseline and final objects are `709fd2a7291382b2cd586179fd4e8e0f0d297fa1c4586b88dd03ea46bdde0cbe` and `e29b07d1c9326a57f98caeda425f542d8e5858a99116c48aff406f1d259281a5`; each replay object exactly matches its corresponding original object. Target logs are empty. The tracked `checks/NativeSelectorClause54.lean` passes against both replay objects with identical expected `#print axioms` output.

Ten replay probes pin each phase target and the rebuilt provider. All 25 target namespace declaration names remain; 24 printed type/axiom reports match and generated public `selectors_one._proof_1` changes its printed type. Sampled default simp and instance registrations match byte-for-byte. A Git-tracked plus nonignored untracked Lean/Python source search inspected 90,633 existing files, including `NativeCellRecipe54.lean`, and found no references to `selectors_one._proof_1`. Printed reports do not establish equality of proof bodies or every persistent extension.

The user-owned untracked `NativeCellRecipe54.lean` is a direct source importer. Its exploratory baseline build was interrupted without a result after a live `ps` reading reported 8,688,456 KiB resident memory at about 54 seconds; no separate process-monitor receipt was saved. It was not tested in either paired lane, and its source was not modified. The `DiophantineConsistency` umbrella was not built. These are coverage limitations, and the wider project, Foundation and Mathlib closure remains cached.

The separately rebuilt `NativeLocalCoefficients54` provider source SHA-256 was `3b48886a210a196d80894669e6bee020d9c751eb16fbf38dc749357b9d0b25df` before and after; its object SHA-256 is `46f14f875d17bc09fb84454c798aa95b89e894604ee69e2581134f29e0619a31`. Its first-path `NativeModesData54` object was pinned at `3dcec3acb6217dfe19f16323c04944fd0f73d5c10a7c05a6453f0854833191d9` before and after. The provider build emitted two pre-existing unused-simp-argument warnings. The initial cached provider object lacked a matching source-current producer receipt. Timings are individual shared-load observations, not benchmarks.

Temporary external evidence, which may no longer be available later, has these SHA-256 hashes:

- `/dev/shm/selector-pos-122-refresh/baseline-records.json`: `74e5cb7c6e5b64e10cd4125f88d106c5cea8ab5cc4c12081871896db1e57d321`.
- `/dev/shm/selector-pos-122-refresh/final-records.json`: `1a59aa4fb26183deeccd6a884fb66ff30db2589f730653ff283b189dabc55ace`.
- `/dev/shm/selector-pos-122-refresh/probe2-records.json`: `f1f9c0d30e1342db91e9c036a69e4734b3560569dfbab9168671bf4c4def0a0a`.
- `/dev/shm/selector-pos-122-refresh/source-search.json`: `69cde4b7145317e61f05343ab12e1a9ecf3a15c2715581b07fb7ee9441bdfb22`.
- `/dev/shm/selector-pos-122-refresh/audit.py`: `548573e3667086d1b8d89e4fd0739dacb8fd60d399faa257c430cfbf0a5723a1`.
- `/dev/shm/selector-pos-122-refresh/audit.log`: `b5b74ff69c727a69b42839e2d7ebfb028481050721bdf4e31c3a6cb0d2c69f18`.
- `/dev/shm/selector-pos-122-target/provider-record.json`: `3e8735cb9c10bfcaf02e091b000824045e57efb9d536b9ee3d18636266210355`.
- `/tmp/selector-pos-122-peer-121.py`: `eab85ee0c66c92355f67d3ef96f2033518cd6e2fa60dc773b3388772d4124d6c`.
- `/tmp/selector-pos-122-peer-121.log`: `b281b31f998c3eeb39d2f6d49714bc6236583b863fe1b87988a97ca3f2f7ab3a`.
- `/tmp/selector-pos-122-peer-121-review.txt`: `135e3adca1a46e1c5927bf324d16ee0984deb96cb3f35eb0df6bebc775863010`.

The independent review checked the target builds, source and first-provider object pins, all ten probes, the generated report change, source search, and parent/commit snapshots. It confirmed the untracked direct client and umbrella are unbuilt. No raw logs or compiled objects are included here; full validation requires the transient evidence and build environment identified above.
