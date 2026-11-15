Marker-separated LCG and LCGS compositions
=========================================
Run: python3 build.py

Two new 194-state compositions, with complete dense/native tables and labels.
The marker/selector separation itself is the existing PA194B construction;
LCG and LCGS are the pinned loop-return incoming parents. This package credits
those mechanisms and proves their exact composition. It does not claim a
sub-194 machine or a new end-to-end Lean theorem.

The included build.py is standalone Python 3.10+, standard library only.
It verifies input hashes, all incoming-edge invariants, all unchanged rows,
four universal two-cell local traces, graph reachability, exact dense hashes,
and both complete blank startup tapes. relative_proof.tex proves in ordinary
mathematics that iPRA can derive H_parent(t) -> H_child(5t) and
H_child(t) -> H_parent(t). This implies equivalent nonhalting sentences.

Novelty against the complete pinned corpus of 520 spanning 194-state action
graph classes was checked separately by the main packet's census tool.
No match occurs under state renaming, arbitrary spanning root, global
reflection, or removal of the final transition's write/move decoration.

Inputs copied from pinned commit793c68737d94bffa4e32a75bce6cc8058d6d22f0:
docs/incoming/pa194_loop_return_2026-11-14.zip,
wrapper pa194_loop_return_2026-11-14, machines/PA194LCG and PA194LCGS.

The numerical source and its absolute calibration are inherited from those
parent packets. The source sites need not be recompiled for this relative
proof: it is a table-level simulation valid on every complete initial tape
with initial control74. The exact initial all-zero tape is used for startup.

New standalone verifier and composition proof generated in this investigation.
Retain upstream parent-packet licenses with this material in the full report.

ADDITIONAL REDUCTION SEARCH

The search/ folder and search_results.tex preserve the bounded optimization
searches from the LCG and LCGMS tables, including stronger joint source
abstractions and all recorded zero-hit results. The portable default replay
completed successfully on 15 November 2026; recorded/reproduction_summary.json
inside search/ records its exact counts. These are not 193-state lower bounds.
