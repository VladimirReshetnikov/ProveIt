# Four-port symbolic byte tuple

`CurrentFourPortBytes.decoded_eq_ports` proves in Lean that natural base-256 decoding of the four symbolic big-endian byte recipes, in beta/K/MC/once-shifted-MF order, gives exactly `CurrentWindowCarry2011.ports`. `decoded_apply` separately makes the decoding of `bigBytes` explicit. The successful source applies the separately checked fully parametric assembly theorem to the two checked decoder pairs; for K and MF it uses exactly the symbolic digit expressions already appearing in those pair hypotheses, while the beta and MC lists remain locally irreducible. This is a Lean-list statement. Lean does not read gzip or files; the separately checked payload comparisons remain external.

Attempt04 passed: actual outer session 69659 exit 0, Lean exit 0, the two expected `[propext, Classical.choice, Quot.sound]` reports, 874 stable recorded direct/companion/shadow guard slots and no stop. The object `/tmp/current2011-four-port-byte-tuple-check04/CurrentFourPortBytes.olean` has SHA-256 `9b94acd4e35406559c61c51c0822798ec56737109415a517de9f973c409daa9f`. Source, child receipt and actual outer observation are retained under `attempt04/`. The successful guard uses Lean `-M2800`, one worker, nice 19, idle I/O, 120 seconds, a sampled 3.5-GiB group-RSS stop and a 10-GiB available-host-memory stop. Direct/provider checks inherit transitive dynamic and package ancestry and do not independently rebuild the base.

The earlier source drafts and failed attempts are retained below. They are not evidence for the successful theorem.

Attempt01 imported the four decoder objects directly. Actual outer session 2269 exited 1, Lean exited −6 at the `-M2800` interpreter memory limit, no theorem report or output object, and the sampled resource stops did not trigger. Attempt02 imported the separately checked [beta/K and MC/MF pairs](../current2011-four-port-byte-pairs/README.md) and used a generic Fin-4 extensionality lemma while keeping the beta list opaque. Actual outer session 76962 also exited 1, Lean −6 at the same interpreter memory limit, with no theorem report or output object and no sampled stop. The exact source, runner, child receipt and separately observed outer exit are retained for each attempt. These outcomes do not show the proposed statement is false.

Both bounded runners used one Lean worker, nice 19, idle I/O, a 120-second limit, sampled group-RSS stop at 3.5 GiB and available-host-memory stop at 10 GiB. Direct and captured producer guards remain in each receipt; they are not a complete transitive dynamic trace or independent base rebuild.

| Artifact | SHA-256 |
| --- | --- |
| attempt01 source | `9c7f3d7c11db1fefd8550625648fe368f1990675f6bc0179a707d6ee687ccb62` |
| attempt01 result | `a9b7f72a0e0ae04ef48c7e5597432122760b830c9c3659587c7094f6a039decb` |
| attempt02 source | `ef57d7294bc796e2c1ce5cd406c3337be56f1e7f04e848186ea014ece5acadf7` |
| attempt02 runner | `bedc507044c0a9531e8e68496460db557dc12e1bb5615a0997cf5b2286a939e6` |
| attempt02 result | `eb12c56c38f5413ac0d5cf2a2e91abae1443b33dc71e86b1d5e5dd9382569c1c` |

Attempt03 applied the separately checked [fully parametric assembly helper](../current2011-four-port-byte-generic/README.md) to the two checked pairs and included a definitional `decoded_apply` lemma. Actual outer session 2118 and Lean both exited 1. `decoded_apply` received a standard axiom report, but Lean's kernel exhausted memory at the concrete `decoded_eq_ports` declaration and the subsequent diagnostic lists the rejected declaration itself as an axiom. Consequently that attempt did not establish the tuple theorem. The exact source, runner, child receipt, log and actual outer observation are retained under `attempt03/`; this was a distinct source-level proof approach, not a successful replay.

| Attempt03 artifact | SHA-256 |
| --- | --- |
| source | `80b6c77ee62fc49dba6e047f90caf350801e72fc4fd3176073b54276f57a5f52` |
| runner | `c60a561147c012aff525a42e7d8712f8706eb7b02f6d41b2f101c43d193c03ea` |
| result | `7d1303ce65bae45724a7c27bc96e5500ad74028b4ae4ef418561dfff368b70f2` |
| compile log | `d24a42d6c5753eb41e4dda7012ed8abcc4a599fd8639bc1375d18de6badf6ff1` |
| outer observation | `ab9536bca846a61cfe8bc77334202d6d9a23522ff0447579f5a99e060ba1e23e` |


| Attempt04 artifact | SHA-256 |
| --- | --- |
| source | `7a36ac70fd6569cecdf79b891535df8f995a18048e7e036e9d2465040676e5f5` |
| runner | `a71762c145af24460b43658baabf76929aa8d81769b18c7b541913df87f0e9d6` |
| result | `606ca5d1e2f13c47921bf472c04ee166273241ff3161bfa42e912c0ba8428691` |
| compile log | `c20e0874abc01f9a07a21e715cd027984be4df24eea05abe6c26e237e6c6a260` |
| outer observation | `8eb3b3e75dd9bfc388a43700a17348288259dc104debe47251923ab7a0f52ee5` |
