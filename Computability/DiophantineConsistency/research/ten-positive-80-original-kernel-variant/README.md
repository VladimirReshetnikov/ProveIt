# Original-kernel specialization of the 80-row graph

This is a distinct **candidate**, not an established consistency equation.
The [fixed symbolic Lean client](../ten-positive-80-symbolic-ipra-client-prototype/FIXED.md)
now asserts the iPRA equivalences for its once-shifted graph without port
premises. Its connection to this JSON and payload is checked externally,
not by a Lean file theorem, and historical provider drift is under repair.
`equation.json` retains the exact 80 ordered rows and ten positive witnesses
of the [directly indexed graph](../ten-positive-unshift-t-finite/data/equation_qcube_V2.json),
but uses the complete retained original-order coefficient tuple. The input
graph's fixed K0 is the directly indexed BFS payload; this candidate's K0 is
the different original-order payload. The other three ports have identical
uncompressed bytes in the two tuples. The exact degree is 750: the external
`verify_degree.py` obtains that upper bound from the rows and a matching lower
bound by substituting `t` for every witness. The diagonal polynomial's
degree-750 coefficient is 12396338 modulo 1000000007. A nonzero coefficient
in this reduction certifies that the integer coefficient is nonzero. This is
not a Lean theorem.

An earlier [external recipe check](../ordinary12-ipra-bridge/compact44-symbolic-k-external-byte-check/README.md)
computes a manual transcription of `paramKernel rho` and matches it to this
original-order K0, not the BFS K0. That is useful for the current Lean
decoder, which uses `paramKernel rho`. The Python check is not a Lean theorem
equating this file with the symbolic kernel, and this candidate artifact by
itself does not establish the iPRA equivalence for its filesystem bytes.

Run `python3 -I -S -B research/ten-positive-80-original-kernel-variant/build.py`
from `Computability/DiophantineConsistency` (or supply its full path from the
repository root). The builder pins the source graph and all four original
compressed and raw payload hashes, rejects optimized Python, checks the 80
rows are topologically valid and recounts the operations. It copies the
complete original tuple and writes deterministic JSON; it does not evaluate
Lean, prove file semantics, or compare the two equations' solutions. The
recorded output hash is
`90bb24c77fab7a19cd4d021e7cd73eda527f71fc361b0aaba6a5f8eaeb1f7be2`.
Run the degree check with `python3 -I -S -B` and the full path to
`verify_degree.py`.
