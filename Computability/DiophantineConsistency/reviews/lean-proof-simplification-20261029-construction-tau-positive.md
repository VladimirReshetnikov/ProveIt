# Construction first-norm positivity validation

Source commit `e400133f9b00e02e0bd3267f8b5ac2b24622a2de`; parent `151f4ca3ff63d7fa7ff43adfc2d7abba30c9f615`. The affected proof is from Claude-coauthored commit `16bbf502706`. It replaces an indirect zero contradiction with positivity of a square and `tsub_pos_iff_lt`; the theorem statement and assumptions are unchanged. The diff removes four net lines.

`ArithmeticConstructionZero.lean` source SHA-256: parent `f756065585fa81fc0cd4ed5e10387cdf9026b3189ed6d1c0e9ef8124f3329e25`; commit `fdef557a958ba7176529795359d5145a0e713ffe8a4a38a1f8609bd59d3e617c`. Both match the tested baseline/final snapshots.

Paired source-ordered target and both direct-client builds passed. Target objects differ; both client objects are byte-identical:

- `ArithmeticConstructionZero`: baseline object `567477b03a31f154fbd7e05a34d67d399e6444124cf8e51b1d95f4ae6eb6ac27`; final `d7df6e08c7d2089edfba036b794f81905bb94499e5f0a3afcee32e161702229b`.
- `ArithmeticConstructionBound`: baseline object `b99aa2b68acf9b93716c38e30381921cdb8bed6ed822990d73a9b72da5f9c259`; final `b99aa2b68acf9b93716c38e30381921cdb8bed6ed822990d73a9b72da5f9c259`.
- `ArithmeticCurrentConstruction2011`: baseline object `4eb80a884111110533ec5c7a16767079f176dc512f334b5096d0264eb4cc95e0`; final `4eb80a884111110533ec5c7a16767079f176dc512f334b5096d0264eb4cc95e0`.

All build logs are empty. Eight probes pin the exact phase target objects; all five target namespace names, printed types and axioms (77 output lines), and sampled global simp and instance registrations match byte-for-byte. These reports do not establish equality of proof bodies or of every persistent Lean extension.

The following direct project input pairs match successful source-current producer records:

- `ArithmeticCarrierSoundness2011`: object `a9b3588787c4ecd29e1d7a16a29d39d8174a48268f4202ba104185b5c4247070`; source `60a28e45d4f0c1776bd7f72cd24197c1c35e1f45abfc9f71f2fefd610cc72c66`; `/dev/shm/pell-y-six-refresh3/records.json`.
- `ArithmeticConstructionAssembly`: object `e7f69999cd0ced816ece92c68ae5ffe60052e3c4802a464c946eee29053d3e71`; source `1cc5bd39c814ab497fd326ec091265fa8f3969e46f54712b9c928b3f45eaba2f`; `/tmp/auxiliary-seed-positive/final-records.json`.
- `ArithmeticCurrentSentence2011`: object `42b8d5c746802687ba40fdaa93304c6c5f0513a5b0f674c8434795081febbfdb`; source `10c1a2e92f05c9765e91fd872050b25c23a94754ec87a0122aebd2e4c90c13e6`; `/tmp/signed-pairs-factors/final-records.json`.
- `ArithmeticLocalNormalization`: object `f78f08081135f5295c9516cd97208d5799818700223c01c3c767ebc84f29006d`; source `5d5c6d4850083c1cc1993cad50da5b88dba39948a034133d19f1d2169f477803`; `/tmp/construction-share/bound-refresh-records.json`.
- `ArithmeticConstructionBoundPell`: object `72057c71a96c2e8d8e28e201d4f6c6f1245cbc0e44664c829aa262b78644bac7`; source `c8e6c082403ef2a1c9c9bd63ea9c96a7bd6e6971d0bb4a187e85ca21c539037b`; `/tmp/auxiliary-seed-positive/final-records.json`.

The final client source-path samples for ConstructionZero reflect the baseline workspace before adoption. The final target build separately links the imported final object to its phase source. The CarrierSoundness final producer pins the current FirstIndex and NegativeNorms objects. Other project, Foundation and Mathlib dependencies remain cached; no full source-current transitive build is claimed.

No raw logs or compiled objects are included. The following transient external files carry the source/build/probe records, review and reproducible independent audit; they may not remain available:

- `/dev/shm/construction-tau-positive/baseline-records.json`: SHA-256 `2a07de1f917a278250108fa3d7b586829c0bb7850a3136c0da44e868241100c5`.
- `/dev/shm/construction-tau-positive/final-records.json`: SHA-256 `d85ead0b70933c85c2f087c12fad3732f18fc8e5576a7493b32b83f4a4447ef5`.
- `/dev/shm/construction-tau-positive/probe-records.json`: SHA-256 `7dd05082bc0aafa6447cea6e02ff8e21b1753e29e4422259eaf1395b7eec084c`.
- `/dev/shm/construction-tau-positive/audit.py`: SHA-256 `22dcda5de6b85c4bda7e096149652292167b889b961445074079e3a866678e3f`.
- `/dev/shm/construction-tau-positive/audit.log`: SHA-256 `047c4fbc37a2a4dbdc5fcd5086c0d65542df70639007b2e999b85cc788a9964e`.
- `/tmp/construction-tau-peer-review.txt`: SHA-256 `e9509d44654ce850f57cbea9ac06bde58defa49d6ae00d1502df995701f918ad`.
- `/tmp/construction-tau-peer-audit.py`: SHA-256 `48804735230007ee807f1a3dacb8c1880e696a9069248cb979cbc03623169a6a`.
- `/tmp/construction-tau-peer-audit.log`: SHA-256 `c768de9a8072bfe42c307826c82944fda161e6d70bde48203f9715fbe4ab0b77`.

The independent review verified all six builds, source and first-path object pins, target-to-client associations, matching client objects and logs, eight target-object-pinned probes, five source-matched provider pairs and parent/commit snapshots. Full replay requires the transient evidence and excluded compiled dependencies.
