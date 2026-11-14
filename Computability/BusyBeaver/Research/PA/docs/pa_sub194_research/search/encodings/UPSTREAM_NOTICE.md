# Provenance of the new encoding searches

The search inputs come from the eight PA194 families named in machine_manifest.json,
from ProveIt commit 2a88cb6a3f823e0de5addf19d725bf8373860c71 and its five active incoming
archives. Their program trees, tables and register architecture retain their
original attribution to the supplied PA research and James Chang's BusyBeaver work.

fold_shift.cpp and fold_bitphase.cpp adapt the corresponding programs in the
supplied pa_consistency_comparison_2026_11_13/physical_search directory.
fold_combined.cpp composes those configuration encodings. derive_contexts.py and
run_batch.py derive and verify the current source contexts, check full blank
initializations and run the new finite screens on the bundled inputs.

reference/symbolic_runtime.py is inherited from the current NS/SUMS packet.
It uses the attributed generic arithmetic-block contracts. This package does
not independently reprove those contracts or claim a new Lean/Rocq theorem.

LICENSE.JamesChang and LICENSE.ProveIt preserve the inherited notices.
See ../../NOTICE.txt and SEARCH_REPORT.md for evidence scope and exact counts.
