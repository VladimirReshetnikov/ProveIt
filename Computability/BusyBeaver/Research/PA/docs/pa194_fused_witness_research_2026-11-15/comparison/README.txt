PINNED COMPLETE RECOGNIZED-TABLE COMPARISON

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 883da8d55452ea097910ed2509a1eefc833ce292

Scope: all tracked .tm, .json and .zip files under
Computability/BusyBeaver/Research/PA and docs/incoming, including nested
archives. All 13,524 selected paths were read and their Git blob identities
checked. There are no missing selected inputs. No arbitrary generator was
executed, and tables in prose or opaque/unrecognized formats were not inferred.
The exact supported JSON forms are documented in reproduce_census.py.

The complete scan records 7,328 table occurrences, 1,380 normalized tables,
and 1,164 spanning graph classes across all sizes. At 194 controls there
are 548 spanning classes and two nonspanning diagnostic byte forms. At 193
controls there are 61 spanning classes, including failed and unproved
research inputs. These are not counts of certified consistency machines.

named_designs104.csv/.json separately lists 104 existing named positive
claims, their source locations, exact graph identity, mechanism, and proof
boundary. All 104 graphs were freshly recovered from literal tables.
packets106.csv accounts for the 100 filed packets and six current incoming
deliveries. mechanism_families.csv is a map of source and physical mechanisms:
its 44 rows are overlapping explanatory categories, not an invariant count
of logically independent theories. Rows prefixed NEW concern this work.
The new four constructions are separate from the 104 existing named classes.

WHAT IS VERIFIED

verify_comparison.py checks all 609 spanning 193/194 representatives, all
seven nonspanning diagnostics, all source-to-name bindings, and exact-byte
coverage of every older catalogued 193/194 class. It recomputes canonical
forms under arbitrary roots and control renaming. For 194 controls it also
allows reflection, bit exchange and ignored halt-entry actions, to give a
strong structural novelty comparison. Bit exchange is not claimed to
preserve blank-zero execution. A transformed positive control exercises
all these symmetries simultaneously.

All four new machines are structurally absent from the corpus and mutually
distinct. Every existing 194-control spanning graph has 194 ordinary
immediate-action bisimulation classes. This rules out only that simple
quotient; it does not prove a 194-state lower bound.

The 22 excluded .tm fragments have zero or multiple external targets and only
2–139 controls. None has 194 controls. excluded_literal_audit.json records
each exact path, bytes, count and unresolved target list. The two 194-control
nonspanning diagnostics are explicitly retained and cannot match a spanning
new graph. These exclusions therefore leave no undocumented 194-control
literal table at the frontier.

RUN OFFLINE

With Python 3.10 or newer and the standard library:

  python3 -B verify_comparison.py --output /absolute/path/replayed.json

This reads the distributed representatives and recorded source manifests.
It does not retrieve the 1.2 GB source corpus or check arithmetic calibration.
To repeat the actual source census against a local checkout containing all
objects of the pinned commit:

  python3 -B reproduce_census.py --repo /path/to/ProveIt --output /path/to/new-census

The census never asks a promisor remote to fetch missing objects. It checks
availability, reads only present blobs, and fails with an explicit missing
list if necessary. The streaming design retains normalized metadata, not
all parsed row dictionaries; the completed scan peaked near 125 MiB of Python
resident memory. canonical.py implements exact ordered-BFS canonicalization
with sound prefix pruning; no heuristic graph match is used.

FILES

summary.json                   Complete census counts and recognition errors.
source_bindings.csv            Every selected path, Git blob, byte size, SHA256.
occurrences.csv                Every recognized table occurrence and class.
classes.json                   All 1,164 spanning classes and first sources.
normalized_tables.json         All 1,380 normalized table identities.
tables/                        All 609 spanning 193/194 representatives.
nonspanning/                   Seven complete but nonspanning literal forms.
upstream_MACHINE_FILES.tsv      Pinned older 18,218-member packet catalogue.
catalog_coverage.json           Exact-byte links covering all 55+528 old classes.
named_designs104.csv/.json      Existing named positive-claim table roster.
packets106.csv                 Filed and current packet descriptions.
mechanism_families.csv          Source and implementation mechanism map.
new_tables/                    All four new complete dense machines.
new_designs4.csv/.json          New counts, hashes, clocks and local certificates.
verification_summary.json       Main conclusions with exact claim boundaries.
offline_verification.json       Completed fresh offline replay.
census_scope.tex               Report-ready detailed scope and qualifications.
new_results_table.tex           Compact report-ready new-results table.

The manifests support reproducibility and attribution. A table identity
or finite execution is not a proof of source correctness or PA consistency.
Those obligations are treated separately in the main report and supplied
source/physical proof components. No new end-to-end Lean/Rocq completion
is claimed by this comparison package.
