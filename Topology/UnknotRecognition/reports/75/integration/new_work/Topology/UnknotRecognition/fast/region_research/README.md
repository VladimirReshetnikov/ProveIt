# Small exact region and diagram integration audit

This directory validates the integration of `fastunknot/pachner_regions.py`
and `fastunknot/normal_pachner_search.py` with the delivered endpoint search.
It is a small finite audit, with no claim of general recognition completeness
or a timing speedup. The audit does not modify either integration module or
the existing independent diagram verifier.

## Reproduction and independent replay

From the enclosing `fast` directory:

```sh
PYTHONPATH=. python -m region_research.audit --output region_research/results/reproduced_audit.json
PYTHONPATH=. python -m region_research.audit --replay region_research/results/audit.json --output region_research/results/reproduced_replay.json
```

The driver can also be run directly by absolute path; it adds the enclosing
`fast` directory to the Python import path. Only Python and the delivered
standard-library project modules are needed. The replay mode imports the
existing endpoint and diagram consumers without importing the region search,
diagram search, move producers, or exterior constructor.

The retained records are:

- `results/audit.json`: complete source triangulations, heights, scope choices,
  wrapper answers, every literal-subset answer and proof, all diagram PD data,
  all diagram answers, commands, interpreter version, source hashes and runtime.
- `results/replay.json`: independent replay totals from the retained record.
- `results/audit_log.txt`: the actual audit invocation's progress and summary.

## Exact finite comparisons

The literal oracle enumerates every subset of the initial tetrahedra and counts
its induced connected components using a separate elementary graph walk. It
does not call the region enumerator. For every allowed subset `F`, it invokes
the endpoint search with exactly that original-cell permission set.

The audit compares the wrapper's output against the union of these literal
queries in two ways: equality of full serialized certificate sets, and equality
of geometric cochain endpoint sets under an exact rooted-traversal
isomorphism key. Full strings and tuples are compared; digests are not used as
an equality substitute. It also checks exact agreement of completed-region and
aggregate-node counts. Every wrapper and literal-query endpoint proof is
independently replayed.

| Supplied source | Region size | Components | Upward allowance | Allowed regions | Nodes | Geometric endpoints |
|---|---:|---:|---:|---:|---:|---:|
| Layered solid torus, 2 tetrahedra | 2 | 1 | 1 | 4 | 8 | 3 |
| Layered solid torus, 3 tetrahedra | 2 | 1 | 1 | 6 | 14 | 5 |
| Two independent inverse bipyramids | 3 | 1 | 0 | 25 | 27 | 3 |
| Two independent inverse bipyramids | 3 | 2 | 0 | 42 | 44 | 3 |
| Two independent inverse bipyramids | 6 | 1 | 0 | 43 | 58 | 4 |

All five wrapper calls return `COMPLETE_BOUNDED_REGIONS`. All 120 literal
queries return `COMPLETE_BOUNDED_FAMILY`. Both exact set comparisons agree in
every case. The wrapper and literal outputs contain 302 endpoint certificates
in total, all successfully replayed. Repeated endpoints across allowed regions
are deliberately retained and counted as replayed certificate occurrences.

## Diagram adapter controls

The nine source-diagram calls retain four `UNKNOT` results with valid proofs:
the single-crossing two-strand unknot, the same source with shellings enabled,
the same source with the empty permitted region, and the crossing-free circle.
These successes concern two diagram sources under the recorded options, rather
than four distinct knots. They contain no Pachner moves; this part of the audit
validates the diagram adapter and source binding rather than new move-search
coverage. Three positive certificates were also rejected against a changed
trefoil source diagram.

The trefoil and figure-eight controls, each using shellings and an empty
permitted region, return `INCONCLUSIVE` after complete exhaustion of that
bounded region family. The single-crossing source with zero node allowance
and with zero work allowance also returns `INCONCLUSIVE`, with no certificate.

The explicit coverage miss is the two-strand braid word `[1, -1, 1]`, named
`cancelled_braid_unknot` in `results/audit.json`. Adjacent inverse generators
cancel, leaving the single-crossing unknot. With shellings enabled and
`max_region_size=0`, the adapter returns `INCONCLUSIVE` with bounded search
status `COMPLETE_BOUNDED_REGIONS`. This is an exhaustion of the tested fibre
and empty-region family, not evidence that the source knot is nontrivial.

The saved independent replay run accepts all 302 endpoint certificates and
all four positive diagram certificates using the unchanged
`verify_transport_disk_certificate` consumer.

## Recorded runtime

The audit records its elapsed wall time and exact command in `results/audit.json`.
Its scope is deliberately small. Elapsed timings characterize the reproduction
run and must not be interpreted as a comparative performance experiment.
