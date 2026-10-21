# Status in the maintained proof checkpoint

This research directory is imported verbatim from upstream `159397838a`, whose original proposal is `4fdc59197a`. Its README and generator describe that upstream construction and its reported focused checks. They are not new compiler receipts for the maintained tree. No supplied generator, Rust search or Rocq compiler ran during this import.

The current [phase-nine Lean checkpoint](../verification/k215/simplification/phase9/README.md) retains its checked representation-independent implication core and adapter. The original drop-in Lean file is recoverable from `4fdc59197a`; current callers also require the composition and lifting interfaces. A generic 52-step adaptation is a promising next simplification and remains uncompiled.

The live Rocq `DomRho8.v`, regeneration record, manifest and `regenerate215.py` retain the exact earlier checked bytes. The proposed four-file change remains recoverable in Git history. Consequently, this directory's command examples do not imply that the live regeneration route has adopted the new derivation. The [merge record](../verification/k215/simplification/phase9/upstream-merge/README.md) binds this boundary.
