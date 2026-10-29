# Annotated context lookup iteration reuse: validation

Source commit `f09fabb788591d03db06cff045e35c087725e690`, parent `7adaea2353a607318e8409075538aa33ee140e84`. The two hand-written inductions now reuse the existing `NatIterate.rec_succ` and `NatIterate.rec_fixed` lemmas, removing eight net Lean lines. Existing statements, assumptions, definitions and imports are unchanged. The earlier proof came from `fac1c28653a`; no Claude coauthor is asserted.

- baseline source SHA-256 `90d9521f6f38d705d263fbb7cc0f2d5ffaef81ee149fbafb4fd05786bb57b58f`.
- final source SHA-256 `1022b46ab0b3c21599059eb6bdedc039719828aa3c38c88f1c5ed32b59977327`.

The paired source-ordered builds of AnnotatedContextLookup, its direct project clients AnnotatedAssumption and AnnotatedRuleSide, and the dedicated checks/AnnotatedContextLookup all passed. Target and production-client logs are empty; check logs match and contain expected printed output with no warnings. The following target/client objects have these baseline/final SHA-256 hashes:

- `AnnotatedContextLookup`: `d8b97b9740a68d27f926285731514ceb2040f31167347bbf197246f5961e25b7` / `74f6d8eaf50bf0d9c5e48b155e76b761f23352b2ffa700e9ee39c9a080cf91dc`
- `AnnotatedAssumption`: `5b5b34ebb2bf66fdce1a92433e4541f99ca18f3a918ebdf18ab635eec513d796` / `5b5b34ebb2bf66fdce1a92433e4541f99ca18f3a918ebdf18ab635eec513d796`
- `AnnotatedRuleSide`: `5dcf2b85bdcea4d2364799c07be5fadb967b8f6fd11692ed2ff4236edbaf6a24` / `5dcf2b85bdcea4d2364799c07be5fadb967b8f6fd11692ed2ff4236edbaf6a24`
- `checks/AnnotatedContextLookup`: `0e05f001a3b3aef758299570172441023ebb39c5d589fdaf6d795c2d8636da3d` / `0e05f001a3b3aef758299570172441023ebb39c5d589fdaf6d795c2d8636da3d`

Both direct-client objects and the dedicated check object match byte-for-byte. Eight probes pin each target object and both rebuilt project providers. All 31 target namespace names, printed type/axiom reports and sampled global simp/instance registrations match exactly. The earlier exploratory direct `rec_succ` variant omitted the generated public `drop.eq_1` name; the final `simpa only [drop]` variant preserves it. These printed comparisons do not establish proof-body or complete persistent-extension equality.

Both project providers were rebuilt from current source before the paired builds:
- `AnnotatedContextPR`: source `b4225674731c3d03ec0d7d80205abbb7573e6aca430a88ec7b36e45735897ab9`, object `b76d0b9594b6db74ec76e7f832df1ea0039dffcd02f1639353dd0092117daf41`.
- `AnnotatedRuleSchedules`: source `e6dd19a55018a64f5dbf9b1be4699876f58394d1c1eb804876b8a07d1effb43f`, object `e9a25bf4f0f034109ab1e77b41d39d59d38f9b66c30c2da4f1b6d92b9ce78961`.

The umbrella was not rebuilt and the wider transitive project, Foundation and Mathlib closure remains cached. The final client input source path for ContextLookup samples the pre-adoption baseline workspace, while the final target build separately links its actual phase object to its final source. Temporary source snapshots, build records, probe outputs and compiled objects are not included in this note and may disappear.

The independently reviewed evidence is identified by SHA-256:

- `/dev/shm/context-drop-shared2/baseline-records.json`: `19afd5356420ddacf5ae9a41b2e328ef826be4ecf2fc002cf6eeda3712ca9b7d`.
- `/dev/shm/context-drop-shared2/final-records.json`: `14addcd87293378528d11eea84e839d9a519ddd7398a79cef2b740aab5cd948d`.
- `/dev/shm/context-drop-shared2/probe-records.json`: `985f99d680acf3da1411397f9b9b378822035f6af1fcd423c60bb9019c9d534a`.
- `/dev/shm/context-drop-shared/common-records.json`: `e6eb2ca51432c96a85af6939b896e6fbbdfb8fc46744ad2f6df17b29263d34ba`.
- `/dev/shm/context-drop-shared2/audit.py`: `1c7bd2ce9ac5c5af16933fff6c12afcbc7a2abf93356bd925a422d4181605236`.
- `/dev/shm/context-drop-shared2/audit.log`: `df52cbe7000e4e3fdf20e82af5d657896249de984802f34c3887ab543712df3d`.
- `/tmp/context-drop-shared2-peer-121-review.txt`: `dfb312bd566023c377d1efc76dc062e2469bcba36e283b799e39d58e6e28159d`.
- `/tmp/context-drop-shared2-peer-121.py`: `571bf9b36c69bbb1d40748ed2bac31f487669692b9d668151ed763aedf013a2f`.
- `/tmp/context-drop-shared2-peer-121.log`: `baabda50c683f593e250f64fc3b2bb63ee75c29822b619b02c482e9b4ed8a858`.

The independent review verifies the recorded builds, first providers, probes, client object identity, source-matched providers, and postcommit snapshots. Full validation requires the transient external evidence, build environment and excluded compiled objects.
