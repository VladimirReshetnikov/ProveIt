# Provenance and claim scope

Repository: [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt).
The fixed review cutoff is
[`aa66d0a33f1f8237a348899eb8095b045a502832`](https://github.com/VladimirReshetnikov/ProveIt/commit/aa66d0a33f1f8237a348899eb8095b045a502832).
The phase-five production baseline is
[`0359ebda60aaf52758358e1450a04988136db67e`](https://github.com/VladimirReshetnikov/ProveIt/commit/0359ebda60aaf52758358e1450a04988136db67e).
The one-commit difference adds exactly the three reviewed incoming ZIPs and
does not adopt their contents into production. Complete observed commit
metadata is retained in `checked/COMMIT.json` and `checked/PRODUCTION_SCOPE.json`.

## Exact received archives

| Repository path under `docs/incoming/` | Git blob SHA-1 | SHA-256 |
|---|---|---|
| `Affine_Proof_Cores_and_Transport_2026-10-21.zip` | `17321c28fc63f3dcdc895fa468eb3cad85d6cabe` | `4b9bf197546985b2c298b15d33bcf256e892a76a749ed1b367fe96aa4c536d46` |
| `K215_Checked_Simplifications_2026-10-21.zip` | `5e489899fef825c91bcbf2889d68ece6238f2251` | `18ec63a7a07bb5614e5002261fe1ce02f219ae0925e7b713df67868663bdb60b` |
| `K215_Certificate_Refinements_2026-10-21.zip` | `7e969e67dfbd88a8b6aca044ce1541115de2f897` | `ae5edcd5fa0496d3fa13178a27b38108ad33a2301d970ebb5f22b968b1f6db0e` |

Original archive sizes are 2,345,161; 1,845,732; and 540,989 bytes respectively.
Their complete extracted trees contain 105, 194, and 106 files. The first
original ZIP is also retained because the independent guarded verifier needs
its exact Git blob. The other two original outer ZIPs and their temporary
transport encodings are omitted; their exact intake metadata and every
received-manifest member remain present. No received archive program was run.

`affine/INTAKE_PENDING.json` is a historical retrieval-attempt receipt retained
unchanged because the independent verifier reads its original Git blob pin.
Its provisional status is superseded by the completed `affine/INTAKE.json`.

Every current or historical source pin carries its own commit and scope.
The bundled phase-five source has Git blob
`c966e0626e98d038d8b4e9300d37414e2ea128ed` and SHA-256
`ccf9e2970482a772bea93919974431c39c442a6c23f83731c0b561c9945fae1e`.
`SOURCE_BINDING_INDEX.json` indexes the preserved source bytes and pin records;
the owned root checker revalidates both SHA-256 and Git-blob hashes.

Recorded compiler receipts, logs, and source hashes are preserved without
upgrading their provenance to a new run. The new guarded-core, positive-trie,
arithmetic and framing proposals remain uncompiled. Finite replay and an
independent mathematical review support their stated scope, not a completed
formal integration. Counts of proof vertices do not count machine states.

Licenses and attributions are preserved in their original received locations
and in `licenses/`. No new blanket license is asserted for all historical or
adapted source files. This release does not modify any repository or earlier
sealed release/delivery, and does not claim a newer production result.
