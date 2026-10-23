# Nine positive variables: signed kernels and higher majorants

Primary endpoint: `generated/split_108_order-1_positive.json`, degree 1,731,700, 462 arithmetic operations. Lower-degree endpoint: `generated/split_108_order4_positive.json`, degree 1,494,006, 487 operations. Intermediate tradeoffs are in LEDGER.json. Each circuit specifies one integer polynomial; node labels are abbreviations, not quantified variables.

Read PROOF.md and section.tex. The theorem is no positive zero iff Con(ZFC), provably in ZFC using the pinned source/compiler and Jones ratio results. These are ordinary mathematical proofs and finite audits, not newly kernel-checked composites.

Run, with Python standard library only:

    python3 build_nine.py
    python3 check_ring.py
    python3 check_nine.py

Also run the sibling encoding/verify_split.py and encoding/test_split.py. Certificate circuits are D^16 times the primary equation, and are labelled explicitly. Natural variants are equivalent translations to nine nonnegative unknowns. Order0 is dominated and retained only as an intermediate audit.

The entire old31 coefficient tuple is supplied under coefficients/old_tuple. Do not replace individual coefficient ports with newer smaller-source ports. The source-system SHA and provenance appear in PROOF.md and upstream/FREE_C_SOURCE_PINS.json.
