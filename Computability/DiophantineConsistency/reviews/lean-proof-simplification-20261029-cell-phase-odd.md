# Cell phase parity simplification: validation

Source commit `128d91fcb5777b8a08d1f8c378bcd34865353403` and parent `32fea77e62a86d8a362387e337b5440d3f085a64` match the tested final and baseline CellDecoding source snapshots byte-for-byte. The original proof came from Claude-coauthored commit `f79467f5448`. Direct simplification modulo two removes the unused Boolean bound and the ring-regrouping/omega argument, for three net Lean lines removed; definitions, statements, assumptions and imports are unchanged.

`ArithmeticCellDecoding.lean` parent/final source SHA-256: `1146b4c394bc5fccd30b808465e2b85598960fa5d07a532e280234516f84b1a4` / `9fb5b1e93c63f29cfa18d5baf0c3ec556fd6860e64366ec00aeedc1b98ff4849`. `ArithmeticWholeField.lean` client source SHA-256: `60ec3e182a625607cf2f15a042b6399ea1e4c0ffaa3249b6c45e56f38335452b`.

Both paired source-ordered builds of the target and its sole tracked direct Lean client `ArithmeticWholeField` passed. The target baseline/final objects have hashes `a614aabc7f5a49f664812775b2def1290b45336a6e9eafad4189bd5fd1ed54ef` / `59436340cd11c7bcc0df6039054e8cc9cd19837320b52555d1782d31810567f4`; client objects have hashes `e0f1d6dc451a40144a3a3427bb7da4eb877f5957836764e0198f1da6996f590c` / `d84270f7b25da84b3b88000cd540c14b1471f930de733e79b38b73a8b416253f`. Both target builds have the same pre-existing `cell_digit` unused-section-variable warning, and both client builds have the same 11 pre-existing warnings; each log pair matches after normalizing the phase path.

Eight probes pin the actual phase-specific target and client objects and the CellTransfer provider. Of 144 common printed declaration/type/axiom reports, 143 match; the generated public `ArithmeticCellDecoding.phase_zero._proof_2` report changes. Generated public names `phase_zero._proof_3` and `phase_zero._proof_4` disappear. No references to the three affected short names were found in a nonignored worktree-wide Lean/Python search. Sampled default simp and instance registrations match byte-for-byte. Printed reports do not prove equality of proof bodies or every persistent extension.

The target's CellTransfer input object `68c652eb8821646f9554b6a96d49a67e42ef790194cc0d08da9be7280a04d6a7` matches a successful current-source producer row in `/dev/shm/mod-nested-share/final-refresh-records.json`; its source is `3b47c2ccf596273b2003eec72562fc3b4cf5fe5b1213fc5ad72fda2b40083259`. The final client's direct target-source path is a baseline workspace sample; its actual final target object is linked to the final source snapshot by the separate target build record. Other project, Foundation and Mathlib transitive dependencies remain cached; no full source-current closure build is claimed.

The independent review verified the paired builds, first-path and source/object pins, target-to-client object links, all probes, generated-name search, matching warning diagnostics, the CellTransfer producer and postcommit snapshots. The reviewer corrected the initial README's inaccurate warning-free client description. Raw logs and compiled objects are not included here; full validation depends on temporary external evidence and build dependencies, which may no longer exist later. Timings are single shared-load observations.

External evidence SHA-256 hashes:

- `/dev/shm/cell-phase-odd/baseline-records.json`: `00d3859bcef2e5308c550e19db7643015e16c402c6568cc648fd8b0589c0548d`.
- `/dev/shm/cell-phase-odd/final-records.json`: `ca6f61d36b32d3a224aed6c9fca6de522710188be1c487483c9678beaf99eee2`.
- `/dev/shm/cell-phase-odd/probe-records.json`: `19690ed6140bc01932a81b78a708ed9056d9110a0512a7a3b44fd6ff1d581ef2`.
- `/dev/shm/cell-phase-odd/README.txt`: `e275718d8948f6a7af1e3a0b691e6bb959daf7d74841df537d851c6d716e1bb3`.
- `/dev/shm/cell-phase-odd/audit.py`: `9bc298c2405b8609437d64a4646efe18e7aa5e99edf1244f2232a315f932c66a`.
- `/dev/shm/cell-phase-odd/audit.log`: `8fdf3ea41cb14e17cf732e6c7339a829280e81d20d527f999e88168d64a18204`.
- `/dev/shm/mod-nested-share/final-refresh-records.json`: `ae11a6827d66850289a5d1ac09b508b0412d8c9220baab88a201c7dfdac3099f`.
- `/tmp/cell-phase-odd-peer-audit.py`: `0391570eace3a139e7e1baaa897885e71cf303e54b7344574082aff02b50c71c`.
- `/tmp/cell-phase-odd-peer-audit.log`: `4b98c07119887f3761c187e801d123e5c154c63878f1478eb4d2e742dff557be`.
- `/tmp/cell-phase-odd-peer-review.txt`: `f653ab2bf528ee7e123137eeadddd0dd5776f9bcad0e07477a2a87c4501a1f35`.
