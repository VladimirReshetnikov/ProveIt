# Zero-auxiliary clipping-table asymptotics

A separate proof packet, 4 October 2026.

`PROOF.md` contains the complete counting, graph bijection, uniform
all-orders expansion, logarithmic and inverse recurrences, justified
sequence-point inversion, exact integer-threshold inverse, and the
zero-versus-one arity proportions.

It also proves sharp signed remainder equivalents and identifies the
leading logarithmic/inverse coefficients with connected labeled graphs
equipped with a proper coloring by two named colors.

`SOURCES.md` records the accepted local dependency pins, existing OEIS and
2023 model-counting literature, bounded overlap search, and the execution
and preservation boundary. There is no novelty claim.

`verify_exact.py` is fresh standard-library exact algebra. Its retained
result checks 66,066 clipping tables, 66,067 weighted bipartite graphs,
33 sequence indices, 231 polynomial values, and formal inverse
cancellation through order six. It never reads or runs upstream scripts.
`verify_connected.py` separately checks the three leading-coefficient
identities through order six against that rational evidence.

For a replay, copy `verify_exact.py` to a new directory, create an `evidence`
subdirectory, and run it there with Python 3.9 or later. It refuses to
overwrite an existing `evidence/exact.json`. `preserve_inputs.py` is a
separate local provenance tool; its original absolute paths are deliberate
and are not needed for the mathematical replay.

All 62 core mathematical input entries are unchanged. No task write went
to Reports 69 or 70; their concurrent release changes are disclosed in the
preservation ledger. No manuscript number, formal-verification status, or
external submission is implied.
