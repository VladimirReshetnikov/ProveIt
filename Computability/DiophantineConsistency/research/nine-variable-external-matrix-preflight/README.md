# Nine-variable external dependencies: bounded Matrix preflight

This packet probes the **22 new source-declared external modules** in the
[nine-variable closure survey](../nine-variable-current-base-source-survey/README.md),
plus the two modules in the already observed Matrix collision. It builds no
project modules and makes no claim that those imports compile together.

The controlled [`lean --deps` probe](direct-result.json) exited 0. Its scratch
source lists the 22 modules plus `Foundation.Vorspiel.Matrix` and
`Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber`. The probe recorded all
reported selected paths and 750 before/after path-and-companion guards in the
fresh-base, package-overlay and toolchain roots. All 24 explicitly listed
objects resolved through the package overlay. `Init` was reported twice at
the same lexical path; the two root candidates have the same hash. No other
direct candidate collision was observed among these modules. This command
only resolves direct dependencies: it does **not** load their declarations,
verify transitive compatibility, or compile the combined scratch source.

The [bounded compiled-header reader](header-result.json) visited 64 objects,
including all 24 direct seeds, and recorded 199 unexpanded frontier modules.
Its actual outer session **76951 exited 0**, with no resource stop; the
sampled process-group peak was 581,009,408 bytes and minimum available memory
was 19,105,255,424 bytes. The reader used the same ordered roots, one Lean
header-reader process, a 64-module cap, a 60-second outer limit, a sampled
3.5-GiB group-RSS stop, a 10-GiB available-memory floor, and idle I/O/nice 19.
It read serialized main/private/server/IR headers and rechecked selected
artifact identities. All 24 seed paths match the `--deps` selections.

The independent Python [analysis](analysis-result.json) rechecked those
results and 1,920 point-in-time candidate/companion paths across the three
roots for the 64 visited names. Among visited main-object candidates, only
`Init` appeared in multiple roots and its hashes matched. It found no route
from the 22 new seeds to either known Matrix module **within the visited
partial graph**; every seed still has unexpanded reachable dependencies.
Therefore this is **not evidence of absence** of a package-transitive path.
No conclusions are drawn for unvisited modules, dynamic loads, transient
changes between observations, or a future combined Lean environment.

Both Matrix modules were deliberately included as seeds, rather than found
as a dependency of one of the 22. Their 20 direct object/companion guards
match the earlier independently reviewed
[two-order import failure](../../reviews/current14-matrix-import-order-probe-independent-v1/README.md):
with those selected objects, actually importing the pair in either order had
previously failed on duplicate `Matrix.map` declarations. The present
`--deps` success does not contradict that observed failure and does not
show the nine-variable extension reaches either conflicting declaration.

An adaptive compiled-header traversal can resolve **recorded static header
reachability** for these roots: follow the 199 frontier names until the
queue is empty, or stop early once a selected conflict module is reached.
Any resource cap must leave unresolved seeds explicitly unknown. The
existing reader currently restarts a partial survey rather than resuming
it; a future resumable, guarded runner would need to revalidate its saved
provider identities and all prior edges before extending it. Even a complete
static header graph would not establish dynamic loads, source-to-object
provenance, or successful combined imports. Before a build, separately
review provider/companion guards, actual project `lean --deps`, resource
limits and how any discovered conflict is handled.

`direct-result.json`, `header-result.json`, `header-observation.json`,
`header.log` and `analysis-result.json` are frozen outputs. The three scripts
are read-only with respect to inputs; `headers.py` refuses to overwrite its
output files. The exact hash list and actual exits are in
[terminal-observation.json](terminal-observation.json). No iPRA theorem is
proved by this preflight.
