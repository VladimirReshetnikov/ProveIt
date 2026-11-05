# Four-port tuple assembly attempts

The source draft aims to combine the four independently checked symbolic big-endian byte recipes into a single `Fin 4 → ℤ` theorem equating natural base-256 decodings to `CurrentWindowCarry2011.ports`. This is a Lean-list statement, with external gzip/file comparisons remaining separate. **No tuple theorem has been accepted in this packet.**

Attempt01 imported the four decoder objects directly. Actual outer session 2269 exited 1, Lean exited −6 at the `-M2800` interpreter memory limit, no theorem report or output object, and the sampled resource stops did not trigger. Attempt02 imported the separately checked [beta/K and MC/MF pairs](../current2011-four-port-byte-pairs/README.md) and used a generic Fin-4 extensionality lemma while keeping the beta list opaque. Actual outer session 76962 also exited 1, Lean −6 at the same interpreter memory limit, with no theorem report or output object and no sampled stop. The exact source, runner, child receipt and separately observed outer exit are retained for each attempt. These outcomes do not show the proposed statement is false.

Both bounded runners used one Lean worker, nice 19, idle I/O, a 120-second limit, sampled group-RSS stop at 3.5 GiB and available-host-memory stop at 10 GiB. Direct and captured producer guards remain in each receipt; they are not a complete transitive dynamic trace or independent base rebuild.

| Artifact | SHA-256 |
| --- | --- |
| attempt01 source | `9c7f3d7c11db1fefd8550625648fe368f1990675f6bc0179a707d6ee687ccb62` |
| attempt01 result | `a9b7f72a0e0ae04ef48c7e5597432122760b830c9c3659587c7094f6a039decb` |
| attempt02 source | `ef57d7294bc796e2c1ce5cd406c3337be56f1e7f04e848186ea014ece5acadf7` |
| attempt02 runner | `bedc507044c0a9531e8e68496460db557dc12e1bb5615a0997cf5b2286a939e6` |
| attempt02 result | `eb12c56c38f5413ac0d5cf2a2e91abae1443b33dc71e86b1d5e5dd9382569c1c` |

Attempt03 applied the separately checked [fully parametric assembly helper](../current2011-four-port-byte-generic/README.md) to the two checked pairs and included a definitional `decoded_apply` lemma. Actual outer session 2118 and Lean both exited 1. `decoded_apply` received a standard axiom report, but Lean's kernel exhausted memory at the concrete `decoded_eq_ports` declaration and the subsequent diagnostic lists the rejected declaration itself as an axiom. Consequently no tuple theorem is accepted. The exact source, runner, child receipt, log and actual outer observation are retained under `attempt03/`; this was a distinct source-level proof approach, not a successful replay.

| Attempt03 artifact | SHA-256 |
| --- | --- |
| source | `80b6c77ee62fc49dba6e047f90caf350801e72fc4fd3176073b54276f57a5f52` |
| runner | `c60a561147c012aff525a42e7d8712f8706eb7b02f6d41b2f101c43d193c03ea` |
| result | `7d1303ce65bae45724a7c27bc96e5500ad74028b4ae4ef418561dfff368b70f2` |
| compile log | `d24a42d6c5753eb41e4dda7012ed8abcc4a599fd8639bc1375d18de6badf6ff1` |
| outer observation | `ab9536bca846a61cfe8bc77334202d6d9a23522ff0447579f5a99e060ba1e23e` |
