# Source-level import intersection after merge 69ca27250b

`receipt.json` records the exact 58-file first-parent changed-file set, and
for each of seven native iPRA targets every recursively resolved local source
path and SHA-256, missing local imports, changed paths in the closure, and
untraversed package import names. Each target has zero changed paths and zero
missing `DiophantineConsistency`, `Foundation`, or `ZFCinPA` modules. The
changed files were in broad inherited guards or unrelated parts of the tree;
this does not imply that arbitrary imported object files are coherent.

This is **only a source-import intersection audit**. It does not validate
`.olean` files, their full transitive provenance, package sources or toolchain,
and it does not constitute an independent post-merge rebuild. The existing
endpoint proofs retain their historical provider ancestry and qualifications.
The audit resolves Foundation sources under the explicit absolute path recorded
in the receipt; it does not cross arbitrary package imports. Run `audit.py` to
generate a new receipt, overwriting the previous receipt, only when that is
intended.
