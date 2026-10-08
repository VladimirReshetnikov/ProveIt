# Reverse suffix determinant responses

`fastunknot.streaming_response` is a standalone experimental compiler. It is
not enabled in the recognizer and does not return an unknot or knot verdict.
It prepares exact modular determinant responses for every suffix of a fixed
classical diagram and crossing order, retaining elimination across stages.

For maximum dart frontier `W`, the proven arithmetic setup bound is
`O(n * (W + 1)^2)`. The proof covers signed weights, singular interiors,
changing face fragments and exceptional primes. Each nonzero response stores
at most `2*b - 1` coordinates for `b <= W + 1` retained black fragments; one
actual fragment remains as a grounding anchor. Interior radical directions
are retained, and a protected nullvector produces an absorbing zero response.

```python
from fastunknot.diagram import Diagram
from fastunknot.streaming_response import compile_suffix_responses

diagram = Diagram.from_braid(3, [1, 2] * 8)
responses = compile_suffix_responses(
    diagram.pd,
    prime=65521,
    max_boundary=64,
    max_stored_elements=100_000,
)
closed = responses[0].query(())
print(closed["value_i"])  # formal Gaussian pair modulo the selected prime
```

A proper-prefix query uses `responses[stage].query(pairs)`, where `pairs` is
an actual geometric matching covering that suffix's boundary labels. The
query checks coverage, inherited coloring and the spherical Euler equation.
Color-incompatible or nonspherical matchings raise `ValueError` and provide
no invariant. Algebraic terminal partitions can instead be queried directly
through `responses[stage].response.query(partition)`; that lower-level method
does not claim the partition comes from a classical completion.

`iter_suffix_responses` yields stages in descending order and retains only
one numerical response unless the caller stores the snapshots. Both APIs
accept a no-argument `check` callback for cancellation or a caller-controlled
work allowance. The iterator accepts `max_boundary`; the collecting API also
accepts `max_stored_elements`. Exhaustion raises `ResponseBudget`. The latter
cap counts retained field entries, not source metadata or the current working
matrix, and is not a hard process-memory limit.

The arithmetic supports checked primes below `2**31`, including 2. Residue-four
Jones inference needs odd moduli and is not implemented here. A modular zero
is not an integer zero certificate. No existing observation policy is changed.

## Reproduce the evidence

Run these commands from the `fast` directory:

```bash
python -m unittest tests.test_streaming_response -v
python response_research/audit_streaming_response.py --output results/streaming_response_audit.json
python response_research/benchmark_streaming_response.py --output results/streaming_response.json --sizes 16 32 64 128 --rounds 7 --large-stream 2048
python response_research/benchmark_streaming_response.py --output results/streaming_response_large.json --sizes 256 --rounds 3 --large-stream 8192
```

The audit independently reconstructs each full cut-face graph and compares
arbitrary terminal partitions with integer Bareiss cofactors. The timing
control rebuilds each suffix independently while using the same symmetric
pivot arithmetic as the new compiler. Timings include source preparation,
geometry, and every suffix response. One excluded warmup verifies per-stage
queries. Two identical dense controls expose timing variation. The natural
and shuffled orders have genuinely different evolving boundaries.

These measurements isolate response setup on explicitly given torus-braid
diagrams. They demonstrate reuse of substantial interior elimination, unlike
an all-terminal repeated-query workload. They do not demonstrate a speedup
of complete unknot recognition: existing filters readily decide this family,
and eager setup of every suffix can be wasteful for an observer that stops
after one early query.

Proofs and qualifications are in the companion article's
`sections/streaming_response_theorems.tex`. The distribution contains the
article under `article/`; its proposed repository location is
`research/presentations_early_certificates/`, relative to the UnknotRecognition
directory. See `../RESEARCH_20261008.md` for integration instructions.
The quadratic width dependence is consistent with established
small-treewidth linear algebra; no new general Gaussian-elimination bound
or general quasi-polynomial unknot recognition algorithm is claimed.
