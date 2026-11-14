ADDITIONAL REDUCTION EXPERIMENTS

No accepted sub-208 construction is present in this directory. These are
finite rejection filters and discovery programs, not minimality proofs.
The complete positive proof is in ../source_optimization/.

INPUT IDENTITY

data/u208_joint.native.tm is the exact Conditional Context Joint-native
208-state table (keep211/delete172), SHA-256:
b348a466a2c316511e0037ea3824de29d4c6ad37338404fbc98a3968fdb25135

data/sites.tsv is the class-A source with the unused CH argument rendered 0.
data/contexts5.tsv is the radius-5 finite context corpus from 15,252 complete
primitive cases plus 48,140 blank startup transitions. The primitive cases
took 6,778,830 literal steps. Windows are 11-bit integers, head at bit5.
data/mask_contexts5.tsv comes from the source-reachable mask corpus: 835,152
complete finite cases and 393,296,588 primitive transitions, plus startup.
The latter has 24,844 distinct state/window pairs; the former has 24,606.

All C++ programs below use C++17. Compile executable outputs into a temporary
directory rather than overwriting any shipped data. The commands assume the
working directory is this directory. No additional libraries are required.

FINITE CONTEXT COLLECTION

    c++ -O3 -std=c++17 collect.cpp -o /tmp/pa-collect
    /tmp/pa-collect data/u208_joint.native.tm data/sites.tsv /tmp/contexts.json

The saved data/observed_contexts.json is the corresponding structured corpus.
To regenerate its TSV, enumerate each state key and each integer in its
contexts array, writing two whitespace-separated columns.

SOURCE-MASK CONTEXT COLLECTION

Generate /tmp/masks.tsv from ../source_optimization/generated/zero_positive_invariant.bin:
each consecutive 64-byte little-endian integer is a 512-bit set for one
source ordinal. Output "ordinal mask" for every set bit. Then:

    c++ -O3 -std=c++17 collect_masks.cpp -o /tmp/pa-collect-masks
    /tmp/pa-collect-masks data/u208_joint.native.tm data/sites.tsv /tmp/masks.tsv /tmp/mask-contexts.tsv

All three positive-value assignments use spare value1; gaps are0,3,4.
This is sampled magnitude evidence, not a quantified interpreter proof.

ONE-ROW FOLDS AND BYPASSES

    c++ -O3 -std=c++17 search_context.cpp -o /tmp/pa-one-row
    /tmp/pa-one-row data/u208_joint.native.tm data/contexts5.tsv /tmp/one-row.tsv
    c++ -O3 -std=c++17 search_bypass.cpp -o /tmp/pa-bypass
    /tmp/pa-bypass data/u208_joint.native.tm data/mask_contexts5.tsv /tmp/bypasses.tsv

The first synthesizes one representative row with a31-step macro limit.
The second rewrites individual incoming rows while attempting to bypass a
deleted state; partial successes are not complete deletions. Saved mask
outputs in mask_results/ contain no accepted complete state deletion.

SHARED SELECTORS

shared_selector/results.json lists18 pairs with equal unaffected rows and
opposite preceding marker bits in this finite corpus. Only three have both
simple three-step providers, and no two share the required provider pair.
The more general dual.cpp synthesizes both selector rows for two folds:

    c++ -O3 -std=c++17 shared_selector/dual.cpp -o /tmp/pa-dual
    /tmp/pa-dual data/u208_joint.native.tm data/contexts5.tsv shared_selector/folds.tsv /tmp/dual.tsv

It found no survivor. Its31-step bounded screen disallows a row candidate
from relying on the opposite, not-yet-synthesized selector row. It therefore
does not exhaust every essentially coupled selector construction.

JOINT SYNTHESIS / OFFSET / TAG SEARCHES

See joint_synthesis/SEARCH_SUMMARY.md for exact counts, action alphabets,
and limitations. The three principal C++ files are synthesize_both.cpp,
synthesize_tag_both.cpp, and head_offset.cpp. The two synthesis drivers take (head_offset.cpp uses the first three arguments):

    table contexts output [macro_limit [deleted_state [radius]]]

For example:

    c++ -O3 -std=c++17 joint_synthesis/synthesize_both.cpp -o /tmp/pa-both
    /tmp/pa-both data/u208_joint.native.tm data/contexts5.tsv /tmp/both.tsv 31 -1 5

The -1 sentinel selects all noninitial deleted states; use0 for the start.
The contexts9.tsv and contexts_spares1.tsv files both use the same Joint
native table. The large branch counts are partial assignment nodes, not
counts of distinct complete machines. Plain joint synthesis excludes new
halt targets; the tag variant includes them. Synthetic exterior tape bits
can make these local screens stronger than actual blank-run reachability.

SOURCE REASSOCIATION

source_research_summary.md records the7,017-layout and12,691-layout finite
walks and their limitations. The paths mentioned there describe discovery
workspace folders; this compact packet retains the positive source theorem
and the reusable finite adapter in ../rotation_repair/vendor/, rather than
every sampled layout. No claim relies on interpreting a nominal random-walk
iteration as an independent extension or on an unverified207-state table.
