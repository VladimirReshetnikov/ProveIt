# Window carry excess bound: validation

Source commit `c78ee90e4ba3b13f6506e253c46c71ffd02fa147`, parent `224e9d7da4eaa93d537f360dee1316a5957c31e6`. The tested baseline and final WindowCarry sources match the parent and commit, with SHA-256 `7663b45a6877e8636e49a1b499a91b6ea9c54f8dff7732dd0d9df584c287ae3f` and `b89c8fcface92fa9e16d45ae50463b557a41254841a4fa9586207244fa8ec25b` respectively. The proof, introduced by Claude-coauthored commit `5fcd5632b3b`, replaces contradiction by a direct product inequality and strict multiplication cancellation, removing one net line without changing the statement or assumptions.

Paired builds of ArithmeticWindowCarry and its sole tracked direct Lean client ArithmeticWindowInterface pass. Target objects differ (baseline `97c9e798fae33817af0ec5a4d4bbe38f16d70361c07783dac6821149ffef3df2`, final `de4abd652e77b221172e470e2bec241527dae196b8137ffe7cb2fe1f2f635137`); both client objects equal `def8ea906ea8c60f27cb9767d0d2ff0dd5ee3234f6ae76fd69e387a0a1e8f1b4`. Client logs are empty; the target logs contain the same existing unused-variable warning after normalizing phase paths and the one-line source shift.

Eight probes pin the phase target and direct CyclicWord objects. All 37 target namespace names, printed type/axiom reports, 29,063 sampled simp registrations and 13,173 instance registrations match byte-for-byte. These reports do not prove equality of proof bodies or all persistent extensions.

Source-matched direct project provider object/source associations were checked against successful records:

- `ArithmeticCyclicWord`: source `890bb35639daad00a18c22c38679fb9bceb3e3bd84c2090e9a785f19e32e1926`, object `3c9d6306288671bd007775c3f97336e321645ebbfb9438911530a49e6b4db611`; producer `/dev/shm/window-positive/final-records.json`.
- `ArithmeticCarrierRadix2011`: source `6668eb76118e9f2910c0f930e1f8f672d0248ecf4bf746b924b3a0aac1bebe5b`, object `5d49d2dc9af2bbd3b694b035d6cdd408755ad94835fc498241c3bacf71a1e119`; producer `/dev/shm/window-interface-gap-131/carrier-provider-record.json`.
- `ArithmeticMaskConstants`: source `dcf27b778181091c3fab210b860ba280e121f6bb267975a07e6231b928072825`, object `a163c4ba3310d00bd565bac0b28edf82b3da5c10ebd3f291bd7c49316d211221`; producer `/tmp/mask-ins-construction/final-records.json`.
- `ArithmeticMaskPopulation`: source `d20988a4349043059eac08c95e331325db736ad08eb27db33adecba7c87879df`, object `566f7b78b5d97b1b1d66bf4c167f3baa002fca66474402f93b03911512a7af46`; producer `/dev/shm/window-interface-gap-131/provider-record.json`.
- `ArithmeticSaturation`: source `7a1a5cd8ff6b2bac9f2dc7fb98211ab0958143eb9dd67318a90a221949f6c964`, object `a4002afe767e2a5d51243934df8e5b7454a320bbc98beb7bfe0ae6730222cff4`; producer `/tmp/saturation-order-simplify/final-records.json`.
- `ArithmeticWindowBits`: source `2c2908c21d9cda638823e679038a52d60b6314a82f97020fc34884e70f9f88af`, object `077506e519c3d74a0f66c137a4e01a2f3069a161011b2f0f220b0c53406250f9`; producer `/tmp/window-digit-replace/final-records.json`.

Final-client input source paths sample baseline workspace WindowCarry before adoption; the final target build separately links the actual final input object to the final source snapshot. Other project, Foundation and Mathlib dependencies remain cached; no full source-current closure is claimed. Raw logs and compiled objects are not included in this note.

Temporary external files, which may no longer be available later, have these SHA-256 hashes:

- `/dev/shm/window-carry-product/baseline-records.json`: `2f7d190d1e7c0649ac3b786fb58ffe4a851ef263b28b15d99b9e3158679dc70d`.
- `/dev/shm/window-carry-product/final-records.json`: `ae0c459de320c5879c8389b2ee378527f492d2a90101908e06d2168601b3f18d`.
- `/dev/shm/window-carry-product/probe-records.json`: `f90180c9a1061d72282588e3f57a70316ab8e6e23e447d7e360f5df654a73415`.
- `/dev/shm/window-carry-product/README.txt`: `976ddaa95077b04d4c2665bb75de345a9a15fc3435c8ca0a3cc1d41f822f7221`.
- `/dev/shm/window-carry-product/build.py`: `e1365c7806656890cda0616579982ff5de311635d52fd41a77b5ca8b5149d096`.
- `/dev/shm/window-carry-product/probe.py`: `8f866b839e54672de4315315deffacb4685839491cc5aed6ba2fa69e47171d3d`.
- `/dev/shm/window-carry-product/audit.py`: `6999c42f1530841afb34655b9d29e046831a3c75fa44ffbfd48c85995278ecf8`.
- `/dev/shm/window-carry-product/audit.log`: `2081b11100756561cec00c6f4c4bd7190e19ee64e606fcb91feb632c9c297a0b`.
- `/tmp/window-carry-product-peer-141-review.txt`: `29377c6e09dd28e49bd3503913aadcdec4c7a447f559fd4ea4d415ee36c8ce48`.
- `/tmp/window-carry-product-peer-141.py`: `0dc3adc7057e1d3102b7a583553db3d6b2385d4b2f4c744c7a0af27f23e3d776`.
- `/tmp/window-carry-product-peer-141.log`: `79ea077364154c50467325520241dd8fe12423518639d8844c605c199a910fbf`.
- `/dev/shm/window-positive/final-records.json`: `da455b6b8edf939747682fe607a0af51155c52c8c0b479c4e2bb03b48aec3bc5`.
- `/dev/shm/window-interface-gap-131/carrier-provider-record.json`: `0c675d85fdf17164832fd5f868fb7a8d6370d1e5e68b4be465426686c930c539`.
- `/tmp/mask-ins-construction/final-records.json`: `60a83439f1431069181794149d373fdc9802bc2fab1d7397bd854b0eb513beff`.
- `/dev/shm/window-interface-gap-131/provider-record.json`: `b6306c356ec4c0e09eb30511073aafc11f8c2a109fcb1f2b50253a944aaa7fc9`.
- `/tmp/saturation-order-simplify/final-records.json`: `384c7bfb150a77ea4b48ccfed2b5ec2d107041b7fd8deeb5e5be90354c8e0b15`.
- `/tmp/window-digit-replace/final-records.json`: `1762bfd5b62946744792a81cfb7cda92b3ac22bb0b1a34572641374e2591f548`.

Independent review `/tmp/window-carry-product-peer-141-review.txt` SHA-256 `29377c6e09dd28e49bd3503913aadcdec4c7a447f559fd4ea4d415ee36c8ce48` checked paired builds, first paths and input pins, all probes, warnings, six provider associations and postcommit snapshots. Full replay requires the transient external evidence, build environment and excluded compiled objects.
