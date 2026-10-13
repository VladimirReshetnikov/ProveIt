# Intrinsic common-port discovery research

`fastunknot.port_subspace.compress_common_ports` is a maintained polynomial
preprocessor. It intersects the blocks' linear port images, adds the
corresponding local equations, and selects nonnegative port rows that
determine the full common port. Re-enumerate local rays after applying it.
It preserves synchronized feasible vectors, coordinate zeros and objective
signs; normalized projective optima can change.

This directory bridges that API to the preserved report-113 atlas. The
ordinary recognizer does not import this research backend. Report 113's
original 46 tests and three audits were run on an external scratch copy.

From `Topology/UnknotRecognition/fast`:

```sh
python -B -m unittest discover -s tests -p test_port_subspace.py -v
python -B -m projective_port_research.audit /tmp/port-audit.json
python -B -m projective_port_research.native /tmp/port-native.json
python -B -m projective_port_research.benchmark /tmp/port-benchmark.json
python -B -m projective_port_research.check_evidence
```

The final command reads retained synthesis evidence, replays source and disc
certificates, regenerates the table and publication record. It uses no atlas
discovery. All scripts use exact arithmetic and the standard library; Regina
is not required.

The new algebra audit compares 2,160 queries to independent whole-source rays
and verifies 768 positive extreme witnesses. The native audit covers all 16
sectors of a two-tetrahedron capped solid torus and six specified sectors on
three- and five-tetrahedron sources. The 202 anchored queries have 69 positive
Euler answers in all arms. The first native sector candidate yields 60
essential discs, versus 51 for either atlas policy: selecting one optimal
positive-Euler witness does not implement a complete disc search.

Seven randomized paired timing rounds and three duplicate controls measure
complete Euler-query batches, including preparation, positive source recovery,
independent geometric replay and serialization. Intrinsic compression improves
the delivered atlas by 1.31–1.99×, but takes 1.60–4.15× the native sector arm's
time. The original benchmark's failed demand for equal disc outcomes is
retained separately. Timing conclusions concern Euler queries with potentially
different chosen witnesses, not equivalent essential-disc discovery.

See `synthesis/intrinsic_port_atlases.tex` for the proof and exponent. There is
no universal small-intrinsic-dimension theorem, no new geometric successor,
and no general quasi-polynomial unknot recognizer.
