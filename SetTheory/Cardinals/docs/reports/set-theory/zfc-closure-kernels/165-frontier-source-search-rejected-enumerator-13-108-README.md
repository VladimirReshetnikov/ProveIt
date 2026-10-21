# Rejected 214-state table

This is a reproducible counterexample artifact, not a successful candidate.

The source adds an existing CB1 component after the enumeration-restoration loop. Its arithmetic proof-search schedule differs by a constant candidate offset and remains a plausible calibrated source transformation. The source has 202 DAG nodes and 4,752 primitive leaves.

A restricted allocator first produced a 215-state table with complete decoder-prefix binding. Two engine rows, (38,0) and (42,0), still entered native state 13. Redirecting both to 108 and deleting 13 produces the included 214-state table, with SHA-256 `575e812c6c435390571e330ded6a2a723e497dffc65da0cd156269c72f8f8614`.

The full concrete primitive check rejects it. At source site 3, instruction CI8 at PC 01010, initialize all nine logical registers to zero, the spare list to [0], and the gap to 0. After 656 machine steps the table returns to the correct next PC 01011, but leaves R8=0 and spares [0]. The required result is R8=1 and spares [0,1]. The complete initial frame, expected and actual results, hash pins, and literal trace are in counterexample.json. This finite counterexample refutes the claimed source-to-machine simulation for this table.

Do not use this table to claim a 214-state consistency machine.
