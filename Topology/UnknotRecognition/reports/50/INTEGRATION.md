# Integration and review boundary

## Proposed change

The additive patch creates:

```
Topology/UnknotRecognition/fast/fastunknot/_sparse_coverage.py
Topology/UnknotRecognition/fast/fastunknot/sparse_incidence.py
Topology/UnknotRecognition/fast/fastunknot/sparse_incidence_verify.py
Topology/UnknotRecognition/fast/tests/test_sparse_incidence.py
```

It does not change the existing dense module, native orbit scheduler, native
orbit verifier, CLI, worker protocol, recognizer dispatcher, or any Rust code.
No remote repository write or commit was made.

Dependencies are the maintained `interval_orbits.py` (including optional count
certificates and `signed_cover`) and `interval_orbit_verify.py`. The exact blobs
used here are in `PROVENANCE.json`; native copies in `snapshots/` are for the
independent offline experiment, **not files to overwrite during integration**.

## API contracts

```python
from fastunknot.sparse_incidence import (
    analyze_sparse_port_incidence,
    analyze_sparse_signed_incidence,
)
from fastunknot.sparse_incidence_verify import (
    verify_sparse_port_incidence_certificate,
    verify_sparse_signed_incidence_certificate,
)
```

Pairings are the maintained `IntervalPairing` objects with inclusive endpoints.
Ports are lists of half-open integer intervals. Retain source pairings as an
explicit list or tuple for replay; a consumed generator is not a source witness. Signed inputs use maintained
`SignedPairing` objects; the parity is separate from the pairing's reversal flag.

The unsigned COMPLETE result has `orbit_count`, `histogram`, and `stats`.
`histogram` consists of positive `[mask, count]` rows in an inclusion-compatible
peeling order. To perform arbitrary lookups, create `dict(result['histogram'])`
and use zero as the default. This is not the dense output schema. Mask zero is
retained when unmarked components exist.

The signed COMPLETE result additionally has `signed_histogram` with rows
`[mask, consistent_count, inconsistent_count]`. Consistency means zero parity on
every closed relation walk. It means orientability only with a validated actual
surface-orientation character.

`strategy='linear'` is the default. `strategy='split'` is an optional balanced
block deletion policy. `record_certificate=True` adds a versioned certificate.
`max_cycles`, `max_queries`, `max_signatures`, and `max_ports` are optional
controls, not geometric promises. Count-cycle and physical-query limits are
shared across the entire signed call, including its base and cover phases.

Internal resource exhaustion yields INCONCLUSIVE with statistics but no
histogram or certificate. External cooperative deadlines use `check()` and
propagate interruption. A cycle count is not a wall-time budget. Certificate
replay needs a separate deadline; serialized input should be size-limited by
callers accepting hostile data.

For exact JSON transport of very large numbers, use the maintained
`integer_codec.json_safe`. The verifiers accept integer fields encoded as
explicit hexadecimal strings and reject booleans in integer fields.

## Minimal usage

```python
ports = [[(2, 10)], [(5, 17)], [(10, 17)]]
result = analyze_sparse_port_incidence(17, [], ports, record_certificate=True)
assert result['status'] == 'COMPLETE'
assert dict(result['histogram']) == {0: 2, 1: 3, 3: 5, 6: 7}
assert verify_sparse_port_incidence_certificate(
    17, [], ports, result['certificate'])
```

## Checks before promoting a caller

The archive's additive patch was checked and applied in a clean local work tree,
then its 21 native-style test methods were run against the exact included native
modules. This is not a run of the complete current maintained suite. After local
integration, run that complete suite and the actual native normal-arc/surface
adapters that will supply ports. Add paired complete-caller measurements before
changing automatic dispatch. In particular, retain all-signatures and
separated-port controls rather than relying only on adjacent/coincident marks.

A successful interval certificate proves a statement about its caller-supplied
relations. It does not authenticate a knot diagram, triangulation, normal
surface, or attachment map. A caller needs its own checked provenance chain.

## Article integration

Keep the standalone article and its table sources together in a research
subdirectory selected by the repository maintainer. Do not directly `\input`
`paper/article.tex` into `synthesis/report.tex`: it has a document class and its
own preamble. A maintained synthesis section should state the polynomial sparse
local theorem, attribute weighted AHT and coverage recovery, describe the sparse
output contract, and preserve the conditional nature of the global target.
