# Source audit

## Repository snapshot

- Repository: `VladimirReshetnikov/ProveIt`
- Pinned commit: `8649990597d73657bde480b6c389de7f85bc0cb0`
- Commit timestamp: 2026-11-16 06:25:29 UTC
- Local research date: 2026-11-15, America/Los_Angeles

The pin is intentional.  The repository was changing rapidly during the audit.
All path and API claims in the report refer to this snapshot or to unchanged
blobs identified below.

## Key audited files

| Path | Blob SHA / observed SHA | Relevant declarations or statements |
|---|---|---|
| `Logic/PrimitiveRecursiveArithmetic/README.md` | `78bf304f4482c7db0ae8cd3a52f3107b23e3c783` | target theory; packet status |
| `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeClausal.lean` | `c5f8ed56c3f33fc4e3449ed9fde65bbbc2c3333e` | `NFm.QFree`, `NFm.unQ`, `Cl`, `Cl.asm`, `Cl.toN` |
| `.../NativeClausalDiagonal.lean` | `889b6145a5a8a75d96cd0c06cb95d2d92246777c` | `KPrf`, `KPrf.subst`, `KPrf.cut`, `KPrf.toNPrf`, equivalences |
| `.../NativeBiInterpretation.lean` | `ccfe499b9687ea0e176f832686d8e492fe15544b` | `NFm.toPRA`, `NFm.ofPRA`, `native_iff_pra`, `pra_iff_native` |
| `Logic/PrimitiveRecursiveArithmetic/Derivations/README.md` | `c9c1a60d782573dfb552d8587e0bfc3f11588911` | checked direct derivation library status |
| `.../IPRADerivations/Core/Basic.lean` | `6b8dc0881e167c8fbcfa9d7e7967302cee92b5ad` | PR arithmetic, `inst`, `ind`, congruence/equations |
| `.../IPRADerivations/Core/Tactic.lean` | `2823ff3c6cafcf4b9713e3176d07324e38406d04` | `allN`, `closeAll`, `deriveNat`, `ipra_ring` |
| `docs/proofs/foundations/ocipra_framework_2026-11-15/README.md` | `49da0612c05ce3bf4d95ccd49a54fa69da330be2` | prior observation-contract framework and status |
| `docs/proofs/foundations/ipra_pfig_framework_2026-11-15/README.md` | `412f2acf2f1f456f552108a031ec273ad2d0fcf9` | prior proof-graph framework and status |

The blob identifiers were returned by the GitHub connector during the audit.
The final package does not vendor upstream source files.

## Repository status relevant to claims

The parent iPRA README states that `ConciseIPRA` is kernel-checked, while the 78
research proof packets were filed without rerunning or compilation.  It also
states that no packet claims a derivation of one of its main theorems.  The new
`Derivations` directory separately states that its listed `Prf PRAAx` theorems
are kernel-checked and have no `sorry`.

This package treats those status statements as authoritative.  It does not
promote packet-level Lean sketches to checked results.

## Compared foundation packets

The audit compared the current foundation directory and prior generated
packages, especially:

- `ocipra_framework_2026-11-15`;
- `ipra_pfig_framework_2026-11-15`;
- `ipra_proof_carrying_observation_graphs_2026-11-15`;
- `ipra_finitary_interface_compiler_2026-11-15`;
- `ipra_kernel_finite_use_framework_2026-11-15`.

The present report reuses their finite-observation, demand, relation, and stable
observer ideas.  Its distinct focus is the direct `KPrf` compiler IR and the
bidirectional exchange with the newly checked `IPRADerivations` backend.

## Environment

Detected:

- Python 3;
- `pdflatex`, `latexmk`, `pdftoppm`, `pdfinfo`;
- PDF render/preflight scripts from the artifact environment.

Not detected:

- `lean`;
- `lake`.

Therefore no new Lean compilation or axiom audit is claimed.
