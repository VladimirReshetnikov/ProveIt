# Independent post-build provider comparison

The worker reported the 425-module rebuild complete and no further canonical
writes before `manifest.py final` captured `final01/result.json`. This
independent check reconstructs its sets from the pinned serialized-import
scan and cone, confirms all 425 cone objects exist, and verifies that 700 of
765 direct-model ancestor objects match the overlay while 65 are absent there.
The 65 are the same module names captured in the earlier manifest; no
overlapping object differs. The full per-module provider paths and hashes are
in `final01/result.json`.

The check compares every live overlay object and companion with the final
manifest twice, verifies the original first-resolved selected direct provider
and companions, and checks all overlapping companion hashes. It also checks
the stage-425 receipt, source snapshot, output object, and recorded guards.
The retained independent observation exited zero with empty stderr.

The final manifest SHA-256 is
`7af1eefd72bdfb476941ae311cd2ddcbfd06d55f2e47e245b2a773679457519e`;
the stage-425 receipt SHA-256 is
`5483e0f8444fcaeaec8a68929f63a77d2aa3435d27fafa1b89c78eed3dc57977`.
This is a point-in-time comparison of selected project objects and their
companions. The 65 absent modules still require their selected supplemental
provider. The result is not a package-transitive, dynamic, complete
source-to-object, or final Lean/iPRA join proof.
