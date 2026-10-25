# Shared certificates for Diophantine consistency

Prepared for Vladimir Reshetnikov and the ProveIt project, 25 October 2026.

This archive contains fixed integer-coefficient polynomials whose non-solvability, on the explicitly stated domain, is equivalent in ZFC to syntactic Con(ZFC). It supplies ordinary mathematical proofs and exact reproducible artifacts. It does not prove consistency, claim a globally simplest equation, or provide a new end-to-end Lean/Rocq certificate.

## Principal results

| Family | Domain | Variables | Degree | Terms | Height |
|---|---|---:|---:|---:|---:|
| Spherical bounds, fewest variables | unrestricted integers | 258 | 4 | 5,364 | 128,446 |
| Spherical bounds, balanced | unrestricted integers | 263 | 4 | 4,141 | 128,446 |
| Spherical bounds, sparse | unrestricted integers | 285 | 4 | 3,750 | 128,446 |
| Signed network, compact | unrestricted integers | 571 | 4 | 19,833 | 1 |
| Signed network, balanced | unrestricted integers | 593 | 4 | 12,027 | 1 |
| Signed network, sparse | unrestricted integers | 646 | 4 | 8,368 | 1 |
| Signed network, sparser | unrestricted integers | 742 | 4 | 7,226 | 1 |
| Pooled digits, fewest variables | nonnegative integers | 221 | 4 | 13,935 | 118,464,197 |
| Pooled digits, balanced | nonnegative integers | 222 | 4 | 9,917 | 83,954,634 |
| Pooled digits, sparse | nonnegative integers | 224 | 4 | 6,527 | 83,953,869 |

Additional tradeoffs are retained in the component catalogs. The eleven-integer family has exact degree / live-operation pairs 316/133, 308/140, 304/144, and 300/148. Its full scalar coefficient height and support are not measured; the six fixed input numerals are completely supplied, not additional unknowns.

For every height-one endpoint, the constant coefficient is one and every nonzero coefficient is either +1 or -1. Natural and unrestricted integer variable counts are not interchangeable. Scalar degree reductions trade more operations for lower degree.

## Read and reproduce

Start with the enclosed PDF. Its editable LaTeX source is in `report/`. Each mathematical component contains its full new proof, exact equation data, source bindings, and reproduction instructions:

- `signed/`: spherical interval guards, adjacent-denominator merging, odd-square radix, quadratic residuals and complete quartics.
- `natural/`: pooled digit budgets, weighted merging and exact-output-bound absorption, with certified nonnegative coordinate restoration.
- `height_one/`: direct cancellation edges, certified row orientations, scale sharing, integer zero-set bijections and complete height-one polynomials.
- `scalar/`: four eleven-variable ordinary polynomial circuits, even-weight and center proofs, exact-degree certificates, all six actual coefficient numerals and their finite reconstruction recipe.
- `prior_direct_closure/`: authenticated retained Round17 arithmetic and logical source dependencies. Its old root closure map and manifest describe the historical full release, not the new subset. See `CLOSURE_MAP.md` here for the active dependency paths.

Run the complete finite verification plan from this directory:

    python3 -B verify_release.py --output /tmp/conzfc_round18_verification.json

This checks the release manifest and runs the explicit component checks, reconstructions and independent audits listed in `VERIFY_PLAN.json`. A finite replay does not replace any unbounded mathematical theorem. PDF rebuilding is separate, through `report/build_report.sh`, and needs the stated TeX/Poppler dependencies.

No network access, repository mutation or publication is part of the computational replay. Scripts may write deterministic check receipts inside their component directories or use temporary reconstruction directories; run on an extracted working copy if preserving original bytes is required.

## Provenance and scope

The comparison snapshot is ProveIt commit `e0c98c629bf10d30b695884f6b1d2ab361bdf513`. Six incoming packages were authenticated, and selected incoming direct coefficient arrays were independently recollected. This is not a claim to have rerun every incoming package or surveyed all literature.

The retained direct logical interfaces are `KEndpoint.c222_iff_zf_refutation` and `ConstructibleChoice.zf_refutation_iff_zfc_refutation`. The scalar route retains the separately pinned source34/native/compiler calibration. Do not mix their coefficient tuples. The new arguments are proved in both directions before composing with those inherited ordinary theorems.

The report identifies which mechanisms are inherited, which are new combinations, and which refinements are new in this round. Further research questions are proposals, not results or commitments to another iteration.
