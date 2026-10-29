# Shared nested-remainder validation

Source commit `8f153edc15ccc37f1b1f54c95888645b7c9f7404`, parent `1e2353e86f22935a7aff48d73a3617d8aaa9349c`. The change centralizes two independently proved nested-remainder divisibility facts in `ArithmeticModularCancellation.mod_mod_of_dvd`. Existing theorems become direct wrappers; their statements, assumptions and imports are unchanged. The edit is line-neutral (eight insertions and eight deletions), eliminates duplicate reasoning, and adds one public theorem. The original CellTransfer proof came from Claude-coauthored `f79467f5448`.

The parent and commit snapshots match their tested baseline and final snapshots:

- `ArithmeticModularCancellation`: parent `2b519d5cc333065c8db60db2b75f460ce42bbc856aefb9920da20095f329e29b`, commit `2f10842ad2446145da3a595b20fa0f85db6e9d6f95285609f07455a8ae885e8b`.
- `ArithmeticCellTransfer`: parent `d972455d407d7efc87307928949b735ee4d0cadf814e39f715fbc1e891e0b49b`, commit `3b47c2ccf596273b2003eec72562fc3b4cf5fe5b1213fc5ad72fda2b40083259`.
- `ArithmeticPellResidueClasses`: parent `a0a54a63e7f7614a0bd08b43c65c49258f25e9f88accec379ee25eef86fba597`, commit `df4884c9c9cc4446163deb37aede62fea410d5d686d89de1e30aa58331bcbe5a`.

Both source-ordered lanes pass all eight modules: ModularCancellation, CellTransfer, PellResidueClasses, ControllerLift, CellDecoding, PellHalfIndex, ControllerData and PellResidueClassesChecks. Separate paired replays refresh the CellLocal/CellLabels chain, Pow/PackingBlocks, and the recently committed PellRecurrence/Periodicity/IndexDivisibility chain. All 30 build rows succeed. The final refreshed target and client object hashes are:

- `ArithmeticModularCancellation`: baseline `9934d2304d6f1e5782aa833431c90215ff8deb0d8c3a819e24ca11e3206ed202`, final `a638651a192ec2fda296d64eb50951b0fcd14b2764b083168509da15db55ec35`.
- `ArithmeticCellTransfer`: baseline `4c1bcca7312649de7e185075c1aff72a79ac5212a056ba1e2fe4a3bf13fe5857`, final `68c652eb8821646f9554b6a96d49a67e42ef790194cc0d08da9be7280a04d6a7`.
- `ArithmeticPellResidueClasses`: baseline `81e0c4d76d035963134cc1aeddd713a3da12af0850e561cf89ee9f9120464c22`, final `a5afe2834ee7419f9b5b7d6ac47a6886891d91a489cf771169b18843ed298867`.
- `ArithmeticControllerLift`: baseline `092a9d642ece6ef39b728f6b7407074b8f8198c46a88939d1cdc82d7dd8c8ada`, final `12e2242642f37288a1bd648a933feb60c59be5fd8c247eaaf437fa89b1cf112f`.
- `ArithmeticCellDecoding`: baseline `d2c49254e3dee4398bf82271477ad531d3438287c51d5de771eca708986f5bdb`, final `eb53d32331e0539f818a91ef9dc55605017da9323354158ec691e80fdba3713f`.
- `ArithmeticPellHalfIndex`: baseline `48a5d87f42447fcbfd7c80c8458158d1e27eb042ecb6ef7876ed09a0f8939450`, final `214bd5f956dfa79be7f668df1625030350b4544ba02948ab429cf480983c5024`.
- `ArithmeticControllerData`: baseline `14c9ff95fa7931f0ae11cf2efa5dee77f539ab3a6894d6da256e2f065c8866c3`, final `3e2c9a136d87c93a5d8612daf15f781032ee2e637d1339ef8e4de97aca0e96c4`.
- `ArithmeticPellResidueClassesChecks`: baseline `dfef2459c6a89143e4e3f4c12e601d0d702627159f2e4f568d909bec067749cd`, final `dfef2459c6a89143e4e3f4c12e601d0d702627159f2e4f568d909bec067749cd` (identical).

Eight combined probes pin all eight phase-specific module objects and eight refreshed providers. They report 240 common declarations with identical printed types and axioms, one new public lemma, and identical sampled simp and instance registrations. They do not prove proof-body equality or equality of every persistent extension. The CellDecoding and ControllerData builds repeat their respective existing unused-section-variable warning in both phases; checks logs contain identical expected `#print axioms` output.

The eight source-matched providers and their successful producer receipts are:

- `ArithmeticCellLocal` object `adc4572fe7fd4b190055e55bde4cae61f603cc22c266eb9e034c030fcbd9b63e`, source `a3eadc1e481d842d81bfa5e334fbca99c46535b9479c51b8fc2df34727a220df`; `/dev/shm/cell-selector-unit/final-records.json` (receipt SHA-256 `ad13da72760df0e600fd8b9d31373f12ee41c702ab062566901ed2c3bcabd499`).
- `ArithmeticCellLabels` object `ff9065671a7e0232527038fa7725a11d02707655f462332f5d7b121476f6651b`, source `096f4d71694efd27060a23e979b0a2cf2736fc1abad641fadbf8663433cc025d`; `/dev/shm/cell-selector-unit/final-records.json` (receipt SHA-256 `ad13da72760df0e600fd8b9d31373f12ee41c702ab062566901ed2c3bcabd499`).
- `ArithmeticCyclicWord` object `3c9d6306288671bd007775c3f97336e321645ebbfb9438911530a49e6b4db611`, source `890bb35639daad00a18c22c38679fb9bceb3e3bd84c2090e9a785f19e32e1926`; `/dev/shm/window-positive/final-records.json` (receipt SHA-256 `da455b6b8edf939747682fe607a0af51155c52c8c0b479c4e2bb03b48aec3bc5`).
- `ArithmeticPow` object `a46405c9e2a29f37da4c6e0ff917d17793da86e9c669602de2fe40b0b55dcf23`, source `d7f033c291d70c5078eacd33c5ce25334f0d64b1bcc8be66e449e88a5b1d7e00`; `/tmp/pow-perturbation/final-records.json` (receipt SHA-256 `1412171380c5eb24bb10d284aaff5d237893c7df4ceb877eddac3d7d458fc140`).
- `ArithmeticPackingBlocks` object `511443f5b5ad420e48edba68f4d9790630d4f377dc758f6743b98e2e84ab02af`, source `29d7a8206cd3c85d117f0b2432917dee1a68034102deca1f169de564542b7526`; `/tmp/cyclic-rot-mod/final-records.json` (receipt SHA-256 `a78225ab616aeed6e4dca9ff3fcba77e5309f632bc53e123c463dca1cb313ceb`).
- `ArithmeticPellRecurrence` object `0b58739aea61f13a516c86ccab1dad0d39021fda50bf84ff91ab3f5cd557d5f0`, source `b2c9d9dc41be16aa503540851c3c9752e2c475a947666f79eb9ea539aebe14af`; `/dev/shm/shared-pell-recurrence/final-records.json` (receipt SHA-256 `25f1a912a593a0ef8360a5c43c36f5de4d8f7a1e555101d27cd64745b555fbee`).
- `ArithmeticPellPeriodicity` object `af38b702578ce3523e47ac5a4c73b3294bc287c53a5f0dd0aff064f9da7e5892`, source `6327f5f4ab6dcf4a2adec32f8fc080588844ea431e0ad58dddb0e4d9b9a3a213`; `/dev/shm/shared-pell-recurrence/final-records.json` (receipt SHA-256 `25f1a912a593a0ef8360a5c43c36f5de4d8f7a1e555101d27cd64745b555fbee`).
- `ArithmeticPellIndexDivisibility` object `b8dfc8d43a583d7c06f1dcb70b9a1d9697ec377943afbc9db878f9c6cafd5a35`, source `fc0e2fc57734a6043a9f43b0877a805ff4b53f76d9e978d7088c9a02a79c5feb`; `/dev/shm/shared-pell-recurrence/final-records.json` (receipt SHA-256 `25f1a912a593a0ef8360a5c43c36f5de4d8f7a1e555101d27cd64745b555fbee`).

`ArithmeticStandardCasts` also matches a current-source receipt in `/tmp/binary-half-direct/final-supplement-records.json`. Other project, Mathlib and Foundation dependencies remain cached; no full current-source transitive build is claimed. Final-phase client source-path samples of changed modules refer to the then-baseline workspace, while each actual phase object is linked to its corresponding source snapshot in its target build record.

The following temporary validation records and independent review are not included and may later be unavailable (SHA-256):

- `/dev/shm/mod-nested-share/baseline-records.json`: `11fe9b8d75c23c550fb0e41ac2c1e4d3313bbeef092746f2758e8db2ab60e201`.
- `/dev/shm/mod-nested-share/baseline-refresh-records.json`: `44e8abc2b2fab9e8f068cdd227c438e7069d8baeb94724d4599c2f02b5f5d24d`.
- `/dev/shm/mod-nested-share/baseline-controller-records.json`: `ff21f92adc139795d3e38230573019de9ad6babdbd5fdafd82f34c8e4cb29600`.
- `/dev/shm/mod-nested-share/baseline-pell-records.json`: `e1ce6081cfbe7af4c41158cded41c42dc8d9262ab5ec7e4f33d74748b81db24f`.
- `/dev/shm/mod-nested-share/baseline-pell-probe-records.json`: `d691ecbaab230994c20d77e606bad90a14f30ae1263409d89814070cbddfec96`.
- `/dev/shm/mod-nested-share/final-records.json`: `6c4dc0db5d49a43755a4e4141c23b0e80a5eb00309042f7ffcc616d446fa737d`.
- `/dev/shm/mod-nested-share/final-refresh-records.json`: `ae11a6827d66850289a5d1ac09b508b0412d8c9220baab88a201c7dfdac3099f`.
- `/dev/shm/mod-nested-share/final-controller-records.json`: `6a5cfb51d1d0d502d6719343a3ba6ba817a7f33c2a8e8cdb0f2e5d43d5d9e71e`.
- `/dev/shm/mod-nested-share/final-pell-records.json`: `f23ea97a4a4930761fc28a4103cf091f825ec0701e4f916053d13fd314c0ec1b`.
- `/dev/shm/mod-nested-share/final-pell-probe-records.json`: `67084422c766fa438a3aa58634c53d8628ac0d51f4edfcd6e14713f3ebf81599`.
- `/dev/shm/mod-nested-share/audit.py`: `ca495e2fb0e421c0fdda1c081ab66ee387bcb35169daf5c4cd98c1a286db0c48`.
- `/dev/shm/mod-nested-share/audit.log`: `1fa5941e8e2916b34c9270e5692a5ba0200233409b657e88a25efc5bd742a033`.
- `/tmp/mod-nested-share-peer-review.txt`: `6fbf4eaf90cd4ba3be65182a862b406d34fff643bbe0768c411884ba83b136e6`.
- `/tmp/mod-nested-share-peer-audit.py`: `0f911cd636c4ed89f1ba724f559aee9f7ad274d7e588a495bc5bd0ffe0b53b1a`.
- `/tmp/mod-nested-share-peer-audit.log`: `d4e3724a4c7e1e0d7eae381a16e0e899dc0494c56349c12a6c5caee39f3298f5`.

The independent reviewer checked all 30 build rows, first-path inputs, replay associations, 16-object probes, warnings, reports, provider receipts and commit snapshots. Raw logs, compiled objects and external records are not included; full replay requires those external files and the build environment.
