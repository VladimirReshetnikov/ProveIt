# Shared boot halt bound validation

Source commit `3912eef4367e8ca6fde337b6541437b0a3c463d2`, parent `ed32d0a4ce7764f841c69faf004bf7f53c806c6c`. The original `ArithmeticRuntimeBound215` argument is from commit `91686596976`, whose trailer credits Claude Opus 5.5. The edit shares the bounded boot-halt proof, removes four net lines across two modules, and adds the public theorem `ArithmeticMachineTape215.boot_halts_le_of_blank`; existing declarations retain their statements and assumptions.

Both target source snapshots match the parent and commit byte-for-byte:

- `ArithmeticMachineTape215.lean`: parent SHA-256 `f4d319ff9dff2a29ded5825d63b89493b1bfc929f6fd140251a7cb5f410908d8`, commit `1b104cbd46260b8f81b2d9528fc16944a63508b1f25d38628d9953ae4b27316c`.
- `ArithmeticRuntimeBound215.lean`: parent `299d4b51a09979eada072d938ea283d114000e07ed2974a43a2222869dc0a23c`, commit `9ea7ded6e1192e589078d987cea53efa337699eedee9b6e114deae91e30cb252`.

Paired source-ordered builds of `ArithmeticMachineTape215`, `ArithmeticRegisterBoxes215`, `ArithmeticRuntimeBound215` and `ArithmeticMachineTape215Checks` all passed. The checks object is identical across phases (SHA-256 `3af04f009266d78c55baa73bdc86669e7d9f92772d6c0234352fa7846788a7bd`); RegisterBoxes and RuntimeBound objects differ. MachineTape, RegisterBoxes and RuntimeBound logs are empty. Both checks logs contain identical expected `#print axioms` output, with no warnings.

The baseline/final target objects have these SHA-256 hashes:

- MachineTape: `d018e7fbc4fa16ea0d11d80919ec7508f4e562502ba8f51b1742d8e5fb213b58` / `97d51f31f5c63f7db3611124201057331dc91070cc798ae116d6d21c503e76f5`.
- RuntimeBound: `81ffafbb5ce5b65dbcbcb32af66cf644b9e28e924a7051de46cdced354b24efc` / `f74de54b1e3ad056487401b8204f679c3710ec857700c89453668bf8a02d356f`.
- RegisterBoxes: `139e33b6086e7fd895154cc61f81f3e08f9635177490131c44c6f3601d9c826b` / `fbf310aa646598161f5241761acd040aa0e70e6cc8a8f4e191fd46025fc7c174`.

The original RuntimeBound builds used a cached `ArithmeticEnumBoundSoundness` object `97c24827ea981b7f881b0536ac1df65b782e94dbb85ce106e724d0c81fd3051b` without a matching source-current producer in the scoped search. A separate paired replay used source-matched EnumBoundSoundness object `5691687562b3aebb3f9234a6d6b280ae31823c65c4cd0b0e20dd2c66ebba37bc` and source `63c431331e80ece05fa2edc3a7b5a1cbcb6d2dc8d3ce633c21355417d2e60a12` from `/tmp/enum-fair-sharing/refresh-cantor-records.json`. Both replay builds passed and reproduced their respective original RuntimeBound objects byte-for-byte.

Three other direct project providers match successful source-current `/tmp/claude-ax-sharing/coherent-common-records.json` rows:

- `ArithmeticMachineRun215`: object `9cd4ca9d5bf60813bed1e1d30fe11d177c67110692f9769b954bd1dc7f499b06`, source `98f0c7004ac5796616bd3d7967a5bed443e7add149456813a0fd2d152a3751cd`.
- `ArithmeticRuntime215`: object `60f0a3907535e3d9b673c1b1d0b9a5380ef5137999cb224c9be7a1b2976ea39c`, source `0ac68ea578f55330504ad8b782c02c33ac7dd24b11cba013cc80a8c07e119d5f`.
- `ArithmeticRuntimeBoundBisim`: object `cf633fd9f2b799f1e2d80466b67add9c485b1ba94314f47599ff6165b120b715`, source `2cc47108d55f39fc07af3fab46b48d29ef0f9b13b5bde1482e514b30d11ec125`.

Eight refreshed probes pin the actual first-path Tape, RuntimeBound, RegisterBoxes and source-current Enum objects. Their reports contain 298 common names with matching printed types and axioms, one new public Tape theorem, and matching sampled simp and instance registrations. These reports do not establish proof-body equality or equality of all persistent extensions. Source-path samples for changed targets in later build rows reflect baseline workspace sources; each actual phase target object is separately linked to its phase snapshot. An initial build attempted RuntimeBound before RegisterBoxes and failed before elaboration; the successful lane corrected the build order. BusyBeaver, Foundation and the wider transitive project closure remain cached; no full source-current closure is claimed. Compiled objects and raw logs are not included in this note.

Temporary external records, which may no longer be available later, have these SHA-256 hashes:

- `/dev/shm/boot-share2/baseline-records.json`: `0bac6229ac38a0160bd6fe1c4d4adacc21dab5872a34d5da780a6990d1a1f24a`.
- `/dev/shm/boot-share2/final-records.json`: `6096df1fbc387b5f82bf527acc56ca568c24314dea7546b2489e29a953ae1865`.
- `/dev/shm/boot-share2/baseline-fresh-record.json`: `73062c7951d9b8e33a3516a458614e087a9990dc75986fb40494d5894b81b189`.
- `/dev/shm/boot-share2/final-fresh-record.json`: `1399e8061ff067f1c64e3da4f6dbda99314e4b26f2d78e2ddde3f3a8e16d851c`.
- `/dev/shm/boot-share2/fresh-probe-records.json`: `5352a1c22fb6afd561d00c52be4ba0e739e626e4a466d6f1e40c4f2cfcda79ff`.
- `/tmp/boot-share2-peer-audit.py`: `ee74883cd9202158c3fa2c0f53c2caca291bf7b3d773a5eb872cc583de4f20a0`.
- `/tmp/boot-share2-peer-audit.log`: `df5ab9059ab00bebf31d4908bc5dc0ecb8f4c8194fe57f2a126732479b3a1e94`.
- `/tmp/boot-share2-peer-review.txt`: `9652216000e4fd5901574e6d4735c6802504ecb5eea2dcdc4bc3295572754233`.

The independent review checked all eight phase builds, first-provider paths and object/source hashes, target-to-client links, both refreshed RuntimeBound builds, eight four-object-pinned probes, the four provider associations, and parent/commit source snapshots. It corrected an earlier claim that the check-module logs were empty; no other issue was found. Full replay requires the external records, build environment and excluded compiled objects.
