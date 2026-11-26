# Source audit

Retrieval date: 25 November 2026 (Pacific time). Read-only GitHub connector; no repository modifications.

## Upstream

Repository: https://github.com/lsernau/grh-lean

Pinned main commit: `72fead102f663d5c7a407964a13dc0cf9d977207` (branch API). All fetched upstream files below are from the main snapshot; file blob IDs recorded where available. No independent Lean build or comparator replay was performed.

| Path | Blob ID or line range | Role |
|---|---|---|
| `README.md` | `fdca72cbfa3557506543b662317267897e0058a0` | proof provenance, two editions, reported status |
| `grh-compact/README.md` | `85d43d83a7fa3b496968ce9216f4a7d75e44e84a` | five statements and reported kernel/comparator checks |
| `grh-compact/GUIDE.md` | `ca70306f0ee22fca325f7f515667e51625e8eabd` | proof architecture and scales |
| `grh/src/Statements.lean` | `1cd1bce93344065936b2b392b23306254e0785ef` | exact RH/Dirichlet-GRH statements |
| `grh/src/Main.lean` | `1adf4187a938510363cdb0dde0a6d628ff39c600` | exported theorems |
| `grh-compact/src/New/Main.lean` | `198ed5bf26aa294898931e0649bc2b88f1389f65` | covolume cancellation, one-sided prime remainder and GRH |
| `grh/src/New/Reduction/MainInequality.lean` | `97f83ab52b2feb420e952a2722b4cef454b9e579` | readable version of determinant argument |
| `grh/src/New/Reduction/Zeros/Criterion.lean` | `5c06362a50e044d491423fb3d830bae6a50c0075` | one-sided analytic criterion |
| `grh/src/New/Congruences/Selmer/RootsOfUnity.lean` | `b5ad128a2c44538e8783050a371e1e44af0c32d1` | selection lemma, lines 46–58, 207–336, 376–514 |
| `grh/src/New/Congruences/Selmer/GeneralTheorem.lean` | `954169c8fbc974a8e56b1b5c467afc944e3b8751` | precise `IsSmallTwist` fields (55–76), character/inertia interface (143–228), finishing lemma (260–322), power substitution and full theorem (325–457) |
| `grh/src/New/Congruences/Selmer/Line.lean` | 596–687 | `TwistPolynomials` construction, uniform number of variables, eventual auxiliary level |
| `grh/src/New/Congruences/Selmer/AuxiliaryPrimes.lean` | 429–448 | designated first prime belongs to tied set |
| `grh/src/New/Congruences/Selmer/SelmerData.lean` | `3ba56f3bcd90bb198b9fd2bff101f3bd2fb8e0c0` | special scalar-inertia and cohomology data |
| `grh/src/New/Congruences/Selmer/StickelbergerSystems.lean` | `b9dfdf5be0fd7ad198d153f9501f3067ad363969` | abstract systems and budget |
| `grh/src/New/Congruences/Selmer/LValueSystems.lean` | `20514d27d180622d60dbd9849f8619f1e5158bfd` | source-specific special-value measures |

Pinned URL examples:

- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Congruences/Selmer/RootsOfUnity.lean#L300-L336
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Congruences/Selmer/GeneralTheorem.lean#L392-L457
- https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Congruences/Selmer/Line.lean#L630-L687

The upstream project is Apache-2.0; this archive contains no copied Lean source. Names of declarations and descriptions are used for attribution and reproducibility.

## Earlier ProveIt analysis

Directory: https://github.com/VladimirReshetnikov/ProveIt/tree/main/docs/incoming

Main branch head retrieved: `47eb73a0c7b2c8495b25bb26d594aec7120ca97a`. Directory listing returned 21 items (README plus 20 ZIPs). Selected ZIPs were retrieved through `fetch_file` with base64 encoding; their central directories were parsed, and selected LaTeX sections decompressed in the connector execution environment. The following two directly relevant reports were read at section level:

- [`grh_method_transfers_2026-11-25(1).zip`](https://github.com/VladimirReshetnikov/ProveIt/blob/47eb73a0c7b2c8495b25bb26d594aec7120ca97a/docs/incoming/grh_method_transfers_2026-11-25%281%29.zip), blob `8392f699e005cbb4bb630195d75785a259374ce0`, `sections/torsion_transfer.tex` and `sections/torsion_literature.tex`. Harmonic bound, total positive loss, bounded power series, infinite packets with finite total budget, matrix consequences, scalar-inertia obstruction. The present note improves the exponent for a fixed finite packet and gives a shell good-fraction estimate, not a replacement of the infinite-packet result.
- [`grh_method_transfers_2026-11-25.zip`](https://github.com/VladimirReshetnikov/ProveIt/blob/47eb73a0c7b2c8495b25bb26d594aec7120ca97a/docs/incoming/grh_method_transfers_2026-11-25.zip), blob `74302df55be1b40664ade24db493235c60859c80`, `report/ramification_budget.tex` and part of `report/sparse_sampling.tex`. Normalized-length ramification obstruction and nonempty bounded support; the present note obtains an order exponent bound and simultaneous multiplicity at one support.

Manuscript inventories also inspected: `grh_transfers.zip` (`10ba8d2ac5e04809d70c468bc79ecdae31dedd19`), `grh_lean_transfer_analysis.zip` (`b0f01e2ea825a07e7a711d4b7059f0fd3421f816`), `grh-lean-transfers.zip` (`ecce11d7f5d919b3c5fed4e310a0ac56ebc0b456`). No claim to have read every archive or all sections.

## Literature reconnaissance

- Daniel Kriz and Asbjørn Christian Nordentoft, *Horizontal p-adic L-functions*, https://arxiv.org/abs/2310.20678. Abstract establishes the relevance to simultaneous twist nonvanishing and David–Fearnley–Kisilevsky/Goldfeld questions; no claim of priority over its full technical contents.
- Vlad Serban, *An infinitesimal p-adic multiplicative Manin–Mumford conjecture*, https://doi.org/10.5802/jtnb.1030; https://arxiv.org/abs/1607.01428.
- Vlad Serban, *On p-adic Versions of the Manin–Mumford Conjecture*, https://doi.org/10.1093/imrn/rnab136.

The new mathematical argument is self-contained modulo elementary p-adic valuation facts and the exact upstream arithmetic interface. Literature search was targeted, not exhaustive, so no publication-priority claim is made.
