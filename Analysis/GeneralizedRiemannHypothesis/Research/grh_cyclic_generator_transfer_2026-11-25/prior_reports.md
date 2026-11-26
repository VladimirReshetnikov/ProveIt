# Prior-report review and access limitations

Repository: https://github.com/VladimirReshetnikov/ProveIt/tree/main/docs/incoming

The GitHub connector listed the following GRH-related ZIPs on 2026-11-25 (Pacific date). Three were accessed as base64 and their central directory and selected TeX headings/abstracts were inspected. This is a targeted overlap check, not a complete line-by-line review of all manuscripts.

| Archive | Review status |
|---|---|
| grh_sylow_transfer_2026-11-25.zip | Inspected abstract, headings and README; blob 735b29d01628744f05bc815d23b534cefd7cf483. Prior general Sylow filter and PSL(2,7) two-pattern example. |
| grh_method_transfers_2026-11-25.zip | Inspected central directory, headings and selected fragments; blob 74302df55be1b40664ade24db493235c60859c80. Prior cubic case, periodic obstruction, sparse sampling, ramification cost. |
| grh_transfer_analysis_2026-11-25.zip | Inspected abstract, headings and README; blob 2ec837a7b74075f98caa840b11ed467dd3e11509. Prior Landau criterion, twist-family reduction, cubic target and K-theory/Vandiver caveats. |
| grh_beyond_dirichlet_grh_2026-11-25.zip | Attempted base64 read; returned content had no ZIP end-of-central-directory record. Not inspected. |
| grh_lean_transfers.zip | Connector returned 404. Not inspected. |

The remaining names were inventoried only:

- grh-arithmetic-transfers.zip
- grh-exponent-six-and-transfers.zip
- grh-lean-transfers.zip
- grh-transfer.zip
- grh_cm_four_terms_and_prime_bias.zip
- grh_cm_prime_applications.zip
- grh_cm_sparse_equations.zip
- grh_lean_transfer_analysis.zip
- grh_method_transfers_2026-11-25(1).zip
- grh_sparse_singular_moduli.zip
- grh_transfer_analysis.zip
- grh_transfers.zip

Correction on filenames: the actual directory listed `grh-lean-transfers.zip` (hyphens), not `grh_lean_transfers.zip` (underscores); the unsuccessful fetch was the latter, a different path. Thus the actual archive was inventoried, not accessed. No claim of a failed read of the correctly named archive is made.

The current report refines the prior Sylow criterion by choosing generators rather than all Sylow elements and adds an independently proved linear Gamma window. It does not certify literature priority. No repository was modified.
