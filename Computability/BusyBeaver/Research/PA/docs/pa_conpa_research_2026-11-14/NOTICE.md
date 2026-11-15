# Attribution and provenance

This research bundle is based on the user-supplied ProveIt repository and incoming research packets at revision `1e1a41f799d4658b829cdd0eabae3775a0c8c4a0`:

https://github.com/VladimirReshetnikov/ProveIt

The G, H, Q, N, AX11, history-fold, arithmetic-runtime, source-language, and proof-calibration mechanisms are inherited and credited to the supplied work. The new contributions are their AX11GH composition, the two concrete machines and their exact certificates, the relative iPRA compiler/transport argument, current-corpus reconciliation and exact novelty audit, and the documented further searches below 194.

The original current incoming AX11H, AX11G, and GH research ZIPs are retained in `references/`. `PROVENANCE.json` binds them by SHA-256 and records source-member relationships for the construction and verification code. The current AX11H ZIP is the mathematical proof dependency; the older filed archive with the same basename is not a substitute.

ProveIt material is attributed to ProveIt Contributors under the MIT No Attribution license. The inherited runtime lineage also carries notices for **James Chang** (MIT) and **Andrew James Wade** (MIT No Attribution). Their full notices/licenses are retained in `verification/reference/`, `construction/licenses/`, and relevant component directories. Keep those notices with any redistributed inherited components. Unchanged upstream archives retain their own notices and metadata.

`construction/vendor/` contains attributed construction helpers. Its inherited fallback repository loaders are unused by the portable constructor, which supplies the frozen parent machine and source nodes directly. `verification/reference/` is the independently retained symbolic interpreter and source resolver. The new checkers are adaptations of the current incoming packets, with family-specific guards, command binder changes, source comparison logic, and physical identities explicitly changed for AX11GH/GHS.

The comparison and search directories contain their own more granular provenance and notices. Some old readmes or saved logs retained there describe earlier snapshots or earlier proof status. The main report, current ledgers, exact new receipts, and pinned current-baseline audit identify which claims are used in this deliverable.

No completed new proof-assistant formalization is represented by this bundle. Python and C++ receipts are ordinary finite or executable symbolic evidence with the scopes described in the report.
