# Native outer-seed witness positivity: validation

Source commit `d13f06b257698bb6d38fa7779294bf1827f32c18`, parent `3f146e1a67354d623cdbea79dc31718dc1dc39f6`. The target source SHA-256 is `201491d6c852eb0d5debf5ed3f852e4a640efe3dae636acd7c77ced3d7edaec5` in the parent and `6601d2e3dff350b82fa2a9c79532d4606e2bb53be3c900b9635735cce94c872c` in the commit; each matches its tested snapshot. The change replaces two zero contradictions with direct positive-product proofs, removing eight net Lean lines without changing the theorem statement, assumptions or imports.

Both initial and refreshed source-ordered lanes passed paired builds of the target and its two tracked direct module clients, `NativeOuterSeedConstructionChecks` and `NativePositiveSourceConstruction`. The root umbrella also imports the target and was not built. Within each lane, both client objects are byte-identical across phases; the target objects differ. Target and checks outputs match across the initial and refreshed lanes for each phase, while the production client output differs after provider refresh. Target and production-client logs are empty; paired check logs contain identical expected `#print axioms` output and no warnings.

| Lane | Module | Baseline object SHA-256 | Final object SHA-256 |
|---|---|---|---|
| initial | `NativeOuterSeedConstruction` | `54a714198fd1460d12a6b8b0effa3ea7b6640bdf288982a7edfa609ac759ea14` | `d1db097cfedd3230f7a14e5e715da8741398099fb269873083ce3dc6aea169fe` |
| initial | `NativeOuterSeedConstructionChecks` | `b65bda4a49a4c0ba4c3aaa83bf642b7700ed5135b3ba50568a086b0bc9b5b0ca` | `b65bda4a49a4c0ba4c3aaa83bf642b7700ed5135b3ba50568a086b0bc9b5b0ca` |
| initial | `NativePositiveSourceConstruction` | `ff2dcc7811244e490b31d7402a93a3f3e61cf9c29dfdd68318d4a14d37d0ad1b` | `ff2dcc7811244e490b31d7402a93a3f3e61cf9c29dfdd68318d4a14d37d0ad1b` |
| refreshed | `NativeOuterSeedConstruction` | `54a714198fd1460d12a6b8b0effa3ea7b6640bdf288982a7edfa609ac759ea14` | `d1db097cfedd3230f7a14e5e715da8741398099fb269873083ce3dc6aea169fe` |
| refreshed | `NativeOuterSeedConstructionChecks` | `b65bda4a49a4c0ba4c3aaa83bf642b7700ed5135b3ba50568a086b0bc9b5b0ca` | `b65bda4a49a4c0ba4c3aaa83bf642b7700ed5135b3ba50568a086b0bc9b5b0ca` |
| refreshed | `NativePositiveSourceConstruction` | `d39a08f656299e0f791d7075d7d1166a11c431045c4dd90a909c122e85a247f0` | `d39a08f656299e0f791d7075d7d1166a11c431045c4dd90a909c122e85a247f0` |

Eight refreshed probes pin the three phase outputs and four provider objects (seven per probe). They show 196 unchanged common printed declaration/type/axiom reports, 12 changed generated public reports (`exists_outer_seed._proof_15` through `_proof_26`), and four removed generated public names (`_proof_27` through `_proof_30`). Sampled simp and instance registrations match. The recorded search covered 90,633 existing tracked or nonignored untracked Lean/Python files and found no references to the 16 affected names. Printed comparisons do not establish proof-body or all persistent-extension equality.

Source-matched project providers in the refreshed lane:

- `NativeHalfBinomial`: source `c816fb0395389dce45042aed6acbfd6c182355357de9d4b2abf660516bab3881`, object `f0c31b9b044df3a48711f0198d98b3075fdaf25555fd137168c8f324d52be715`; receipt `/dev/shm/native-outer-positive-111/provider-record.json`.
- `Carrier66Source`: source `c4c9db61501f2130998be82af68fa200d848a9bd1175f15a2ac4431eb4879388`, object `1112777627137313862dbadd9cf6908fc3df0a86886487777bfcf93e40962d83`; receipt `/dev/shm/native-outer-positive-111/carrier-provider-record.json`.
- `ThirteenFreshSeed`: source `6ebf7f8df7557638a5be8e2e44aba62e65e214e51306e87037aac6a55f86dd2b`, object `422676d8eb9005a4b2af4bf7ebabcfb38e97287d3ef0da649b571f74fa763a18`; receipt `/tmp/current-packing-positive-sharing/refresh3-records.json`.
- `NativeRankVariation`: source `46c226eba0018eb15eaec66bb31b2ea8af7682fbef76d0245ee45c6aa236ef73`, object `290f134da2e422c0fd8554b49341a453a92342813846a093cbef7044f20a0679`; receipt `/tmp/kernel-residues-sharing/coherent-refresh-records.json`.

`NativeHalfBinomial` and `Carrier66Source` were rebuilt from current source with before/after pins. The initial lane used a NativeHalfBinomial object with only a single source sample and older client-provider objects. Final-client direct-input source paths sample the baseline workspace before adoption; the actual target object is separately tied to its final source by the target receipt. Other project, Diophantine paper and Mathlib transitive inputs remain cached; no full source-current closure is claimed.

Independent review checked both lanes, first-provider paths and source pins, rebuilt provider receipts, seven-object probes, changed/removed generated names and source search. Postcommit verification confirmed parent and commit snapshots. Raw logs and compiled objects are omitted; full validation requires the following transient evidence and environment:

- `/dev/shm/native-outer-positive-111/README.txt`: SHA-256 `4157d7f44a27847d054074f623af622b5c8c680e290b249a552c552a9343ebfd`.
- `/dev/shm/native-outer-positive-111/build.py`: SHA-256 `181f710224abc9a026627e89bf5da3cd8eb2af8c3053457d18480f8a84a21011`.
- `/dev/shm/native-outer-positive-111/refresh-build.py`: SHA-256 `9511eebc8a413801e1e72ba7325c16743d0365b67ba965cf10c35ce89deddcb2`.
- `/dev/shm/native-outer-positive-111/baseline-records.json`: SHA-256 `27700f3d451cccea5eb36d7ca725ac5008f83af14d26d4ada27a406e4d37b8bf`.
- `/dev/shm/native-outer-positive-111/final-records.json`: SHA-256 `e6a7bd36dd6576ec9e77a1e41cb6b71bccd864ff6deb6eded08730f78d3876a3`.
- `/dev/shm/native-outer-positive-111/baseline-refresh-records.json`: SHA-256 `af1dae6b7459902d8ecc695a7a9e02758812e7fb7835ac455109cdd53c8deec7`.
- `/dev/shm/native-outer-positive-111/final-refresh-records.json`: SHA-256 `646758803258efe2716a80b032fd0eeb0702b84c3334f9d131b2e57bf18d2339`.
- `/dev/shm/native-outer-positive-111/provider-record.json`: SHA-256 `7c6d6b4b936c0473be0dbd5038b491df4c567884abc6339b52099f2337679229`.
- `/dev/shm/native-outer-positive-111/carrier-provider-record.json`: SHA-256 `65722ac4e620a66fa7a67230546c58fcbd6feaf36d68358d4df5c292839aa0ee`.
- `/dev/shm/native-outer-positive-111/probe-records.json`: SHA-256 `a81136046ea17fe5c1e5befdb03bafd7ff157f56e75ae27d145a8b8f85eb5113`.
- `/dev/shm/native-outer-positive-111/reference-search.json`: SHA-256 `aa02683c1d5d8c0e5a3651280d430b252d31284533f9fd71cf0053a9c73f21e0`.
- `/dev/shm/native-outer-positive-111/audit.py`: SHA-256 `f533dcb2e125ca6331b5430c7c04aa0ebfb9a3eb76df45b6c3042028621e8c89`.
- `/dev/shm/native-outer-positive-111/audit.log`: SHA-256 `08244a15b24b7e971a51a5da9d94ed863a3d3613818a0f39580c84cbfc9fefb7`.
- `/tmp/native-outer-111-peer-review.txt`: SHA-256 `5930367bb5bf11d8f4322b2008ba3a2a9fcf0e8f17237e975dd565603fd4440f`.
- `/tmp/native-outer-111-peer-audit.py`: SHA-256 `70c37845d5e1b9cfb168e2243fe91469e1bfc9f5d84f5519174dad8f0619a5f4`.
- `/tmp/native-outer-111-peer-audit.log`: SHA-256 `468be15705138c730068faaddb5395e6ea67324279c3147930688d01049c13b7`.

Timings are single shared-load observations, not a benchmark. Earlier `nlinarith` exploratory attempts failed on natural subtraction and are not part of the adopted proof.
