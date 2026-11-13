# Split cut 04: exploratory result

This follows the original draft's failed 64-row direct kernel check. In exploratory wrapper session 27472, the two 32-row parts `CompactRelabelChunk04A` and `CompactRelabelChunk04B` and their exact list take/drop join each exited 0 without warnings or `sorryAx`; the wrapper actually exited 0. Their author-provider outputs are not a paired or independently audited replay. `CompactRelabelAssembly.lean` now imports the joined cut rather than the failed monolithic source, but the assembly is still uncompiled.

Cuts 00–04 and 14 have compiled in author-only checks. Cuts 05–13, the assembly, the color and row-index bijections, and all-model tile transport remain unproved. `check_arrays.py` is a separate external check that the three draft array literals match the independently reviewed finite relabeling receipt, with two mutation controls; it does not itself prove those arrays correspond to the Lean row functions or that they are permutations inside Lean.
