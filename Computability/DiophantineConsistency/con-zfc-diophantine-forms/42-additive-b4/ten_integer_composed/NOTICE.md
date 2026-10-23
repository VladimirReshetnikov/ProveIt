# Attribution for the composed ten-integer instance

This directory combines two new constructions in this delivery:
the B4 source-coding adapter from ../ten_integer/ and the complete
nonzero683195 native compiler tuple from ../coefficient_backend/.

The outer arithmetic construction, original sparse parent, and circuit
infrastructure derive from Vladimir Reshetnikov's ProveIt collection,
pinned at 22e75dd6b87b1b199bb08c778d7cf075ae5aae08. The base contribution
retains attribution to package31, Sun's 2021 and 2026 papers, and the
classical Bose--Chowla construction. Read the base directory's NOTICE.md,
SOURCE_PINS.json and upstream_SIGNED10_PROOF.md for the original chain.

New work in this directory is finite coherent rebinding, explicit transfer
through the positive parent (including multiplier and transport
conventions), recomputation of 402 fixed coefficient bounds and beta_S,
and regeneration/audit of the combined main circuit. The comparison
instance is unchanged.

SOURCE_PINS.json identifies the inherited source files and new sibling
artifacts. source_proofs/ORDINARY_BLANK_PROOF.md and
source_proofs/QUARTIC31_PROOF.md are byte-exact source copies, verified
against their Git blob identifiers. Their mathematical theorems remain
inherited dependencies. The copied parent JSON is byte-exact too; its old
tuple metadata is superseded explicitly by data/INSTANCE.json.

Original repository and third-party license/notice files remain in
licenses/, LICENSE.upstream31 and NOTICE.upstream31.md. The literal K215
machine attribution and calibrated proof endpoint are inherited, not
newly claimed.
