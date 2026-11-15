# Model-valued spare-tail site 28 and 29 controller bridges

These model-theoretic sources have passed a staged source replay; its physical and foundational prerequisite stages remain prebuilt, as detailed below.

The repository-source combined loop replay also passed using this directory
for the source-directory arguments and the same retained staged inputs.

* `/dev/shm/pa194-site28-dynamic-controller/PA194SourceSite28DynamicPhysical.lean` (`abec7dfd02e44ab7effaed3666cfc635a6b96d3ba8c9469b4afd238e29b52c45`), `sourcePhysical`, advances the actual encoded controller 28→29 and the matching physical frame for any model-valued suffix count. It assumes `args 10 = repeatOutput(count,0)`, returns an updated logical register 8 and an extended suffix of count+1, has an arbitrary controller-file tail, and supplies an existential physical clock. Its input and output gaps are `(k+1)+1` and `k+1`.
* `PA194SourceSite29DynamicController.lean` (`a55dd65327201c92de8d743b8f73582c0fc6c9c16b720ea0d745b2911c0461ed`) checks that literal site 29 increments logical register 6 and advances to site 30, including identification with the dynamic physical output's logical registers.
* `PA194SourceSite29DynamicPhysical.lean` (`43ec75d82744e7a882473ff692b9b43e2631b0a0e922b699012a233044cf8c1b`), `sourcePhysical`, uses the same suffix premise and arbitrary model count for a matching controller/physical 29→30 segment, extending the suffix once. It preserves the gap `(k+1)+1` and supplies an existential physical clock.
* `PA194SourceSite28Then29Dynamic.lean` (`1127cd8a2210b88c27b446ab2c7c80ee87a71a4ae2ac85c06a1e315253e1b497`), `twoSteps`, composes both segments with the first output suffix matching the second input; the count is incremented twice and the initial/final gaps are `((k+1)+1)+1` and `(k+1)+1`. The controller tail is arbitrary. It gives two exact controller steps and two successive model-valued physical clocks.

All are PRA model theorems; they do not give a uniform all-site simulation or any consistency implication, nor do they assert a native iPRA proof. The physical premises are model-valued and do not require a fixed standard spare count. Their current logs are `/tmp/pa194-site28-dynamic-physical.log`, `/tmp/pa194-site29-dynamic-controller.log`, `/tmp/pa194-site29-dynamic-physical.log`, `/tmp/pa194-site28-then29-dynamic.log`; axiom reports do not contain `sorryAx`.

The prerequisite physical suffix replays are in progress: `/tmp/pa194-site28-dynamic-complete-check.log` and `/tmp/pa194-site29-dynamic-complete-check.log`. The subsequent staged source replay of the controller and bridge modules passed; because earlier exploratory search roots overlap and the replay retains prebuilt physical roots, it does not establish coherent full transitive object provenance. The separate fetch common-source audit has a different closure and does not itself certify these physical bridge modules.

`PA194SourceDynamicLoop.lean` (SHA-256 `7dbe58403af330ce49ae9eeca42587b2b12b67d5fe5e9e927a02f221c07cc114`) adds `fourSteps`, a scratch-checked 27→28→29→30→27 loop under the further hypothesis `args 0 = m+1`. It composes the checked 27 positive branch and site-30 jump with the two dynamic increments. Its physical frame gap grows by one, and the suffix count by two. It provides three existential model-valued clocks and the fixed site-30 jump clock; it does not yet supply a primitive-recursive cumulative clock or a model-length iteration proof.

Both dynamic physical prerequisite stages have now passed independent staged replay with exit 0. The combined controller/physical source replay passed with exit 0, with log `/tmp/pa194-dynamic-source-loop-replay.log`; its wrapper is `check-dynamic-source-loop.sh` in this directory. Its full invocation is the documented 19-argument command in `/dev/shm/pa194-site28-controller/SEED-CONTROLLER-REACH30.md` with these six additional arguments in order:

```text
/dev/shm/pa194-site28-work/build-site28-dynamic-complete
/dev/shm/pa194-site28-work/build-site29-dynamic-complete
/dev/shm/pa194-site28-work/build-one-spare-file-roundtrip
/dev/shm/pa194-site28-work/build-site30-jump
/dev/shm/pa194-site28-dynamic-controller
/dev/shm/pa194-site29-dynamic-controller
```

The source controller and bridge suffix are rebuilt together into the wrapper's temporary output. The several independently replayed physical stages and general foundations remain prebuilt; the wrapper rejects nonidentical overlaps among machine stage objects, checks selected direct baseline and source hashes, and checks axiom reports. It does not rebuild or authenticate their complete transitive closure, and it inherits the code-graph overlay provenance limitation. Do not treat this replay as passed before checking its final `PASS: dynamic ... loop` line and actual process exit status; an earlier PASS line refers only to the older four-step seed check.

The combined controller/physical source replay completed with exit status 0. All the new bridge theorems and the four-step loop were checked without `sorryAx`; the complete final log is `/tmp/pa194-dynamic-source-loop-replay.log`. Its stage-overlap audit confirmed equal bytes for overlapping machine objects. This is a staged source replay, not a full transitive rebuild of the machine and foundations.

The site-28 exact-clock source is `/dev/shm/pa194-site28-dynamic-controller/PA194Site28DynamicClock.lean`, SHA-256 `bf325c6583c582161ded1ef274fd64cba238c70f932b8c3425d807396ffec4c5`. `exactClock` proves one concrete model arithmetic clock for the full site-28 physical segment, without existentially choosing that segment's time. It is still not a full primitive-recursive `Code` for the cost. Its source suffix replay passed with exit 0, using `check-site28-dynamic-clock.sh`, `/tmp/pa194-site28-dynamic-clock-replay.log` and `/dev/shm/pa194-site28-dynamic-clock-replay`; the source checker and machine-stage object receipt are in the adjacent `/dev/shm/pa194-site28-dynamic-controller` and `/dev/shm/pa194-site29-dynamic-controller` directories. The common site-27 baseline and earlier physical/foundation objects remain prebuilt. From the repository root the exact command is:

```sh
/dev/shm/pa194-site28-dynamic-controller/check-site28-dynamic-clock.sh "$PWD" /dev/shm/pa194-site27-coherent/build /dev/shm/pa194-site28-work/build-carry-seven /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site28-work/build-site29-selected-return /dev/shm/pa194-site28-work/build-finish-return /dev/shm/pa194-site28-work/build-site28-dynamic-complete /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site28-dynamic-controller /dev/shm/pa194-site28-dynamic-clock-replay
```
