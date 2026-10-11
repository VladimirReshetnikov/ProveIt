# Source provenance and scope

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `445f754610e1377939235794de84ed9075fc09f5`.

The research comparison uses the TeX and editorial source files in `Analysis/Polylogarithms/docs/manuscript`, its `chapters` directory, and the five polylogarithm archives plus README present in `docs/incoming` at that commit.

`snapshot_manifest.json` records 85 inspected payloads, each with its commit-pinned source URL, byte length, Git blob SHA-1, SHA-256, and verification flag. The Git hash was recomputed as SHA-1 of `blob <byte_length>\0<payload>`, not as plain file SHA-1. The originally retrieved identities were independently rechecked against directory metadata requested at the immutable commit. Every inspected file matches.

The canonical compiled PDF and `source-inventory.json` were not downloaded in this pass; the editable TeX sources and editorial ledgers were used directly. These two metadata-only entries are named in `snapshot_verification.json`. A matching file hash establishes provenance, not correctness of every theorem in that file. The source audit and novelty comparison are targeted to the claims described in the article and integration ledger.

The incoming archives were expanded without absolute paths or parent traversal. Their included source sections were used to distinguish existing results from the new continuations. Downloaded repository content and third-party papers are not copied into this deliverable; their identities and citations are sufficient for retrieval.

The article's bibliography identifies the classical analytic inputs. The June 2026 Kara Öztürk–Can preprint was available only through its primary abstract; it is cited for scope and attribution, not used as an unexamined proof dependency. Historical priority for the new-relative-to-repository identities has not been established by an exhaustive search.
