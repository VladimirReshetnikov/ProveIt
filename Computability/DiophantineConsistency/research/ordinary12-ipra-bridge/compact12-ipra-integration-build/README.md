# Prepared compact-first integration overlay

`prepare.py` created the fresh selected overlay
`/tmp/compact12-ipra-integrated-20261102/lib`. It rechecked the previously
verified compact model-equivalence provider roots, compared every common
relative filename with the nine-variable endpoint provider, selected the
compact side for every conflicting module family, and suppressed foreign
companions. It removed the nine-base objects/companions for 59 statically
affected endpoint modules so those old artifacts cannot silently be used in a
future source rebuild. The compact `AdaptiveEquationSyntax2011` object is
selected rather than rebuilt. The result contains 2,557 selected live files;
133 relative filenames overlap the nine provider and 100 differ. All selected
compact roots were mutually compatible by the recorded full-file comparisons,
and the recorded provider inventories were unchanged during preparation.

The 59-module list is a **static source-import starting hypothesis**, not a
verified transitive object closure. In particular the selected compact object
and the unrebuilt nine-provider objects require provenance and actual import
ancestry checks before the overlay can be treated as a coherent proof build.
An independent source review found that the compact-selected
`AdaptiveEquationSyntax2011` and its 11-module pinned source closure match
the historical coexistence provider, but that review also retains the gap
between source imports and serialized object imports.

The first diagnostic `ReadObjectImports.lean` was interrupted manually after
approximately 50 seconds at low CPU with no output (exit 130). It obtained no
serialized import data and is **not** a successful metadata check or Lean
build; the exact source and observation are preserved under
`observations/metadata-attempt01/`. `ReadObjectImportsMinimal.lean` is an
untested smaller-import alternative. No Lean compilation has been run in the
prepared integration overlay.

The preparation manifest with all selected file hashes, resolved paths,
overlap conflicts, omitted families and source pins is
`observations/attempt01/manifest.json` (SHA-256
`36ee7a0c7b881cefffafebd7d3a3ff678aec8010ca2019fe71dc8ff8ed29486e`).
It records a point-in-time guarded preparation, not a paired replay, a full
package/dynamic ancestry audit, or an iPRA proof.
