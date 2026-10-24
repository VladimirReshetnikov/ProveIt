# Provenance and licensing

The comparison repository is VladimirReshetnikov/ProveIt at commit
85ae4070019efd66ea3e58e9a67d287528094e8b.

The byte-pinned natural parent and its complete original package come from
`docs/incoming/ConZFC_Synchronized_Certificates_2026-10-24.zip`. They are
preserved under `source/` and `upstream/synchronized/`. The parent has its
own older calibration snapshot and source notices, retained unchanged.

The unchanged `terminal_elimination.py`, `verify_projection.py`, and
`audit_common_radix.py` are from
`docs/incoming/con_zfc_batched_certificates_2026-10-23.zip`, component
`con-zfc-batched-certificates/integer/`. These supply the previously published
within-repository signed monic projection mechanism. The new contribution
is the selected-domain-guard construction and its combination with the
newer synchronized parent, together with the complete literal endpoint,
ordinary proof, and separately authored independent checker.

`SOURCE_PINS.json` gives exact immediate-source file digests. The included
MIT No Attribution license governs the new code and text as well as the
received projection files; inherited notices inside the synchronized
package remain applicable. AI assistance was used in this contribution.
