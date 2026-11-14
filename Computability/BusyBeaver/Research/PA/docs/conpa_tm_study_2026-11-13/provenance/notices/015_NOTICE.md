# Attribution and provenance

This package was prepared for Vladimir Reshetnikov's request to compare the
three supplied U211 Con(PA) proposals and obtain a candidate below 211 states.

New work consists of the exact three-way comparison; the compatible U210
composition; the shared-helper eight-factor reassociation and combined U209
reduction; their mathematical arguments; independently authored finite
certificate checkers; fresh final-table runtime/startup verification; and
portable reconstruction, reporting, and packaging.

The input theories, numerical proof calculus, source proof-search program,
earlier state reductions, and compiler/runtime architecture are inherited
from the supplied ProveIt research collection and its credited predecessors.
The four original archives are retained unchanged, with their nested
dependencies and attribution/license material.

Specifically:

- `code/source_language.py` is copied unchanged from the Contextual U211
  archive's `code/source_language.py`. Its historical attribution and docstring
  are retained. It supplies tree syntax, closure signatures, and CFG routines.
- The four `.py` files in `code/runtime/` are copied unchanged from the Rotated
  U211 archive's `checks/native56/`. `code/runtime/PROVENANCE.json` preserves
  their earlier source identities and hashes. Some historical docstrings refer
  to the original authors' preparation context; they do not describe new
  authorship in this package.
- The runtime's imported `check_startup.py` is used only for its table loader.
  Its older standalone startup decoder is not used to justify the new machine.
  The separate new `code/check_startup.py` performs the complete calibrated
  interior-startup check used by `reproduce.py`.
- The independent new finite checkers `code/check_u210.py` and
  `code/check_u209.py` do not import the discovery or package builder.
- The complete original Research, Contextual, Rotated, and unary-theory ZIPs
  remain in `inputs/`. Original notices within them are preserved, including
  the m254/K215/K230 lineage and Wade compiler attribution where supplied.

No repository-wide relicensing of inherited material is asserted. Refer to
the unchanged original archives for their file-level licensing and notices.

Audit prose may record preparation-time workspace paths. Those paths are
historical explanatory notes, not active dependencies. All reproduction
paths in this release resolve relative to its extracted directory.

The new candidate has an ordinary mathematical, executable verification;
it is not a newly kernel-checked end-to-end PA consistency theorem. The
report's proof-status distinction applies to every summary in this package.
