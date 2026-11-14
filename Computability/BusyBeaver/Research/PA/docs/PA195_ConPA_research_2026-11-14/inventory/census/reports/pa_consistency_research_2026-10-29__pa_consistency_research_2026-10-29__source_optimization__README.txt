VERIFIED SOURCE SPECIALIZATION: 3909 -> 3904 PRIMITIVES

This folder is complete and self-contained. Run:

  python3 verify_source_optimization.py

The script requires only Python3 standard-library modules. It validates the
pinned original source, computes both source CFGs by two independent methods,
reconstructs the optimized source, checks every surviving instruction and
control-edge projection, and proves the needed guards by finite inductive
abstract invariants. All checks remain active under python -O.

Read PROOF.md for the ordinary mathematical halting-equivalence proof.
Read generated/result.json for exact metrics and hashes.
verification_receipt.json records byte-identical ordinary/-O outputs.

Result:3904 primitive occurrences,5076 ordinal edges,200 distinct syntax
subtrees,address depth42,maximum zero run6. Original:3909 primitives,
5083 edges,197 subtrees,address depth42,maximum zero run6.

This is a source-level improvement. It supplies NO literal machine with fewer
than208 states and NO new proof-assistant kernel certificate. The increased
subtree count means the primitive reduction cannot be read as a state saving.
