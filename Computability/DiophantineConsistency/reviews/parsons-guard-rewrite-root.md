# Guard descriptors under rewriting

`ParsonsGuardRewrite.rewrite` proves that a `ParsonsGuardPrefix.Guard`
descriptor survives every rewriting of free variables by terms. In the
universal case, the proof preserves the freshly opened variable and shifts
the rewritten terms using Foundation's `free_rewrite_eq`. This is needed when
opening one side shifts the remaining marked side context.
`all_sigma` constructs the descriptor for one universal with a Σ₁ body.
Neither theorem asserts that every Π₂ formula has a descriptor.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. Both
axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-guard-rewrite-replay/FILES.json) has SHA-256
`14abbf4af73321c600259745ce42fd5953a769d0a4cd4100bdecd64ccf38fe32`.
The direct `ParsonsGuardPrefix` source hash
`9a3731f3e23aaf4b8ea22c5c98f7c0856bb0622afb2d8b8ffc93172018c9e3cf`
matches its frozen snapshot, and its object hash is
`94b4e3517408fa0069c373cde58693a77b693c05b0ba7cb54daac862c8a625ca`.
Earlier provider chains, Foundation/Mathlib, and completeness objects remain
an inherited boundary, not a fresh transitive source audit.

This supplies descriptor stability and a one-universal constructor. Handling
multiple marked sides, general Π₂ normalization, the global well-founded
recursion, conservation, and the PRA-provability target remain open. The
separate HA result for the maintained 14-variable PDF equation is complete.

A third independent replay at `/tmp/parsons-guard-rewrite-build-j_j8arr_`
passed with matching sources, objects, and complete logs, under the same
inherited-provider qualification.
