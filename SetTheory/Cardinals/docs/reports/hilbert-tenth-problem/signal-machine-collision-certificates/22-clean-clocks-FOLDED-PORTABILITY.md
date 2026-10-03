# Portable adaptation record

The eight emitted JSON circuits, eight text DAGs and all nine pinned reference files are unchanged from the independently audited folding release. The original full manifest is preserved as original-MANIFEST.json. Original and delivered hashes are recorded in the outer delivery-provenance.json.

Two authoring-path references were adapted for a portable public copy:

- The audit note uses /path/to/original-base-packet in the optional live-base command
- The checker destination guard uses the adjacent reproducibility directory, computed from __file__, instead of a fixed authoring-workspace path. This guard does not read that directory. Normal replay consumes only this addendum's local pinned references. The optional --check-live-base argument still selects and authenticates an explicitly supplied full base packet

The checker math, complete affine identities, source inheritance, domains, counts, degree computations and corruption tests are unchanged. Its self-hash-bound independent receipt was regenerated. The portable manifest accounts for the adapted files and this record. Historical audit logs retain their original checker hash and are labeled as historical evidence; fresh portable normal and optimized replay are recorded by the enclosing release.
