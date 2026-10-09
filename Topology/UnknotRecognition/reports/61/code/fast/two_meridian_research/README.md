# Maintained sparse two-meridian search experiments

These fixtures, frozen baseline and benchmark driver come from report 47.
The baseline at commit `2b93767bd3cf7ea7c1995acd66f50c72858a30c5` has SHA256
`5eb36230e9b9114df0f42c089ab716bfd6473ba4baf1621182170ef1a30e7b0d` and is
byte-identical to the maintained module immediately before this integration.
The optimized search preserves its arithmetic, certificate format and exact
first-successful derivation. It changes closure initialization, filters pairs
under a checked trivial-singleton condition, and prunes pairs in proper closed
sets. Productive-unary inputs retain exhaustive pair enumeration.

Run from `fast/`:

```sh
python -B -m unittest discover -s tests -p 'test_two_meridian*.py' -v
python -B two_meridian_research/audit_search.py --output results/seed_audit.json
python -B benchmark_two_meridian_search.py --output results/seed_benchmark.json
```

The benchmark separates standalone exhaustion of the two-seed class from a
knot verdict. `INCONCLUSIVE` after exhaustive failure is a completed class
query, never a proof of knot type. Whole-pipeline `UNKNOWN` measurements remain
censored in the raw data. Every conclusive standalone result includes replay.
The arms isolate stamped state reuse, candidate restriction and closed-set
pruning; an identical baseline control checks timing variation. The pipeline
comparison also includes disabling the optional stage.

The ordinary pipeline still defaults to `use_two_meridian=False`. Search has
an `O(n**2)` word-operation bound on diagrams with trivial singleton closures;
the productive-unary fallback retains its cubic search bound. Neither statement
changes the conservative complete-stage arithmetic bound or establishes a
general quasi-polynomial recognizer.

Native evidence and the updated theory are in `../synthesis/sparse_seeds.tex`
and `../synthesis/data/sparse-seeds-*`. The report's original historical timings
remain in `../reports/47/snapshot/Topology/UnknotRecognition/fast/results/`;
they are not substituted for measurements of the maintained pipeline.
