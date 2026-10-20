# Attribution and licensing

This research contribution was prepared for Vladimir Reshetnikov's ProveIt
repository. The new prose, scripts, certificates, and construction are
provided under the MIT No Attribution license in `LICENSE`.

The mathematical and implementation starting points are:

- ProveIt, pinned to `ad8cbe8249445f43408617e88a0edb668b00248d`;
- the unchanged Source124 archive `K225_Construction_2026-10-19.zip`;
- the logical proof subset of ProveIt Source116, restored byte for byte with
  original paths and hashes in `portable/theory/source116/restoration_manifest.json`;
- Elliot Glazer's K230 Rocq development, pinned by the predecessor to
  `3142e4dd980f0be12f4abb636c4ae2528afc17eb`.

The two runtime-engine Python modules and the inherited machine numbering
map are copied unchanged from the predecessor. Their byte identities are
checked by the aggregate reproduction. The new independent machine-fold
checker and the two new finite logical certificate checkers are separate
implementations, with the precise independence claims described beside them.

The complete predecessor archive is retained unchanged, including its
provenance, manifests, proof sources, and license notices. In particular,
the vendored K230 development includes notices for LibTactics, the
Undecidability library, BusyCoq, and Wade. Those third-party components retain
their original license terms. The MIT No Attribution license for this new
contribution does not replace or remove any third-party license.

The present report adds a K-specific restricted-equality calibration, the
canonical-helper source adapter, the 224-state construction, the conditional
K interpretation, and their supporting proofs and verification records.
It makes no global priority or minimality claim.
