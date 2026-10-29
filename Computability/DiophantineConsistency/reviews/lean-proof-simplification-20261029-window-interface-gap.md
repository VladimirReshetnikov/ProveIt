# Direct window-gap bound validation

Source commit `a43f8695f63ffc5220ff9ad45d1bde68256a5c46`, parent `d3baf45019f6d1145a42a935eb1808f3b0ee5cc3`. The old strict-bound argument came from Claude-coauthored commit `d2a666efce2`. Applying `tsub_pos_iff_lt` after reassociating subtraction replaces a contradiction, removing three net Lean lines without changing definitions, imports, assumptions or theorem statements. Both parent and commit sources match tested snapshots: SHA-256 `e54a86bca6207c478a149c7c194bff0c030f2aee7c8322e02798fe45954ba3d8` / `5026471145aca946886f07fe32f82d5b3aca1bcb00875eb8f16a4e8bdf3c337d`.

Paired source-ordered WindowInterface and both tracked direct clients WindowZero and CellWindow passed. Target and client logs were empty. Baseline / final compiled-object SHA-256 values:

- `ArithmeticWindowInterface`: `eadcc1cf8adcd2e4f8ef6624dacc61b7936334c4bc31218ff57f7284c44c3084` / `def8ea906ea8c60f27cb9767d0d2ff0dd5ee3234f6ae76fd69e387a0a1e8f1b4`.
- `ArithmeticWindowZero`: `2afa5bfc2aff5c6a5479e8f9c24fa03cb984347559d848876174304f749d3e5b` / `7fa1bc696a3bd60733f4382aee821fd16449a8d158ef821a8213497bf8692228`.
- `ArithmeticCellWindow`: `8cafdf57dd07b7eba48346fa6a4fb16ce5d5047b497bf81312c0d6afe2e6fcf1` / `8cafdf57dd07b7eba48346fa6a4fb16ce5d5047b497bf81312c0d6afe2e6fcf1`.

Eight probes pin all three phase objects plus CarrierRadix2011, MaskPopulation, Saturation, WindowCarry and Occupation. All 48 combined namespace declaration names and printed type/axiom reports match byte-for-byte; sampled global simp/instance registrations match. These reports do not establish proof-body or all persistent-extension equality. CellWindow objects match; WindowZero objects differ.

The following direct project input source/object SHA-256 pairs are linked to successful source-current producer receipts:

- `ArithmeticCarrierRadix2011`: source `6668eb76118e9f2910c0f930e1f8f672d0248ecf4bf746b924b3a0aac1bebe5b`, object `5d49d2dc9af2bbd3b694b035d6cdd408755ad94835fc498241c3bacf71a1e119`; `/dev/shm/window-interface-gap-131/carrier-provider-record.json`.
- `ArithmeticMaskPopulation`: source `d20988a4349043059eac08c95e331325db736ad08eb27db33adecba7c87879df`, object `566f7b78b5d97b1b1d66bf4c167f3baa002fca66474402f93b03911512a7af46`; `/dev/shm/window-interface-gap-131/provider-record.json`.
- `ArithmeticOccupation`: source `0fa4f2828ecf51eb1ca2a89b97d3645e309e522beaa0dabb1437adbbc91ba7ff`, object `a88346adc5625d9477086f899c912bbe141f10d74da2a4c5011b7c24c31df835`; `/dev/shm/window-interface-gap-131/occupation-provider-record.json`.
- `ArithmeticMaskConstants`: source `dcf27b778181091c3fab210b860ba280e121f6bb267975a07e6231b928072825`, object `a163c4ba3310d00bd565bac0b28edf82b3da5c10ebd3f291bd7c49316d211221`; `/dev/shm/window-positive/final-records.json`.
- `ArithmeticSaturation`: source `7a1a5cd8ff6b2bac9f2dc7fb98211ab0958143eb9dd67318a90a221949f6c964`, object `a4002afe767e2a5d51243934df8e5b7454a320bbc98beb7bfe0ae6730222cff4`; `/tmp/saturation-order-simplify/final-records.json`.
- `ArithmeticWindowBits`: source `2c2908c21d9cda638823e679038a52d60b6314a82f97020fc34884e70f9f88af`, object `077506e519c3d74a0f66c137a4e01a2f3069a161011b2f0f220b0c53406250f9`; `/dev/shm/window-positive/final-records.json`.
- `ArithmeticWindowCarry`: source `7663b45a6877e8636e49a1b499a91b6ea9c54f8dff7732dd0d9df584c287ae3f`, object `37fd311250f63d044543cfc07c43f6f9155fc704f3a59162f92c83ce20a37ac0`; `/tmp/window-carry-tail/final-records.json`.
- `ArithmeticHalfBinomial2011`: source `5bc6e8e8dd6cff53c280cffbd289420ee208f12079059162c335df11ff35b36e`, object `25f93a33447668423d9d0215ca760965aa23baf34217c325081b347b26a38e25`; `/tmp/four-positive-wrappers/refreshed-final-records.json`.
- `ArithmeticCurrentSentence2011`: source `10c1a2e92f05c9765e91fd872050b25c23a94754ec87a0122aebd2e4c90c13e6`, object `42b8d5c746802687ba40fdaa93304c6c5f0513a5b0f674c8434795081febbfdb`; `/tmp/signed-pairs-factors/final-records.json`.
- `ArithmeticWangSoundness`: source `ab60524c7c5ca33443db3aec90c67d9875a306e5ead1f93eedf2c95776519a2e`, object `62f512d7ef2467e6660725b4ef7264102fb86fcce4af278296f0ffd35eae6748`; `/tmp/wang-initial-sharing/records.json`.

CarrierRadix2011, MaskPopulation and Occupation were rebuilt from current source. Occupation's provider build has two existing linter warnings; the other two provider logs are empty. Other project, Foundation and Mathlib transitive inputs remain cached; no complete current-source closure is claimed. Final client direct-input source paths sample the pre-adoption baseline workspace, while the target build separately links each phase object to its source snapshot. An initial lane omitted Occupation and stopped before CellWindow elaboration; a second lacked WangStrip and failed at import. The successful lane corrected both overlay issues.

Temporary external evidence, which may no longer be available later, has these SHA-256 hashes:

- `/dev/shm/window-interface-gap-131c/baseline-records.json`: `a64349440ed9e5e2cc2208084efb7f7bbcf04501a8ee690d85b3b4ac378e8362`.
- `/dev/shm/window-interface-gap-131c/final-records.json`: `fc83fc9aa672556c6606697b2fe16f5e2487f6bd7e387ecae28059f46cec6b13`.
- `/dev/shm/window-interface-gap-131c/probe-records.json`: `b5ec0f8fb380670ed3ebf885deea47bc388daa9052e2c4108c2b82d88c369ccf`.
- `/dev/shm/window-interface-gap-131c/audit.py`: `4ad36e1b6410849538e6aa3b94bb8372b5ba9597ca511acf1245421ab15f6103`.
- `/dev/shm/window-interface-gap-131c/audit.log`: `6a7963d1183e8e20ef0ce41ba3f4c2385ee836e6f9a2802fde0af1dd6fef81f5`.
- `/dev/shm/window-interface-gap-131/provider-record.json`: `b6306c356ec4c0e09eb30511073aafc11f8c2a109fcb1f2b50253a944aaa7fc9`.
- `/dev/shm/window-interface-gap-131/carrier-provider-record.json`: `0c675d85fdf17164832fd5f868fb7a8d6370d1e5e68b4be465426686c930c539`.
- `/dev/shm/window-interface-gap-131/occupation-provider-record.json`: `d641912c92cf3befa48a444319115eb15665d159cba6de30233a9f0d1f1737d3`.
- `/tmp/window-interface-gap-131c-peer-133.py`: `267ae4db5200793329b230c5d85ab8b5a08548be98994fddbaaa9a00c7195c5e`.
- `/tmp/window-interface-gap-131c-peer-133.log`: `0ec62c31858f468ebfd99a0c1519bcd27c7a72213f88f54c0483c1d9d568abbe`.
- `/tmp/window-interface-gap-131c-peer-133-review.txt`: `9cef82d3304ba16c0458f2f35813dee6781ae56d1475c3fb8ee17d64e2083cce`.

The independent review checked all six builds, actual first paths, source/object pins, all eight probes, ten provider associations and commit/parent snapshots. Full replay requires the transient records, build environment and excluded compiled objects. Raw logs and compiled objects are not included here.
