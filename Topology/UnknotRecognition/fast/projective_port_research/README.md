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

## Complete continuation after rejected witnesses

`filtered.py` adds support clauses excluding previously rejected source
extreme rays. A union-mask dynamic program enforces all clauses jointly at
each atlas vertex. Support incomparability preserves every other extreme
candidate, and support descent preserves the clauses. The extra factor is
exponential in the number of rejected witnesses, which remains an unbounded
geometric parameter in general. Default caps return inconclusive; caller
cancellation and inspection exceptions propagate.
The inspection predicate must be fixed and decide each candidate exactly:
an unsupported or capped inspection must propagate, never return a false
acceptance flag that would permanently exclude an unresolved candidate.

```sh
python -B -m unittest projective_port_research.test_filtered -v
python -B -m projective_port_research.filtered_native /tmp/filtered-native.json
python -B -m projective_port_research.filtered_cubes /tmp/filtered-cubes.json
python -B -m projective_port_research.filtered_benchmark /tmp/filtered-benchmark.json
python -B -m projective_port_research.check_filtered
```

Six tests include 480 independent filtered-cone comparisons and exact positive
ray exhaustion on sixty models. The filtered native search agrees with complete
sector-ray inspection on all 202 queries: 60 certified discs, 142 completed
absences, recovering all nine single-witness misses. It uses 220 positive-oracle
queries and 374 mask transitions, with at most one rejection per query.

Full geometric-query timings now compare equivalent answers, with an initially
empty geometric witness cache in each arm. The filtered atlas is 3.07–7.70×
slower than the native sector method on the five measured batches. An abstract
scalar-port cube family verifies that rejection counts can grow as `2**m` even
at port dimension one. Neither the algorithm nor these examples change default
recognition or establish general quasi-polynomial complexity. See
`synthesis/predicate_filtered_atlases.tex` for the full proof and evidence.
