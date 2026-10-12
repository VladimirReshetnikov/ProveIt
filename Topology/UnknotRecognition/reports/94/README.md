# Modular Morse Certificates for Compressed Unknot Hierarchies

Research continuation prepared for ProveIt, 12 October 2026.

**Read `article.pdf` or build `article.tex`.** This package proves and implements
polynomial encoded verification and fixed-template offset synthesis for supplied
interval Morse matchings. It does not implement a general quasi-polynomial unknot
recognizer and does not change the native recognizer.

## Main results

The article's theorem “Exact modular compilation and independent replay”
is the synchronized modular-rank compiler: binary interval inequalities
reduce to two wrap classes, exact floor-sum counts and difference constraints.
The article also proves an exponential lower bound for contiguous affine ranks
in fixed source coordinates, a modular path certificate, relative product
collapses and a genuine regular three-dimensional product lift. Component-local
rank composition is proved but not implemented in this release.

The geometric implication is conditional on an **authenticated regular PL
cellulation of the specified 3-manifold**. A combinatorial rank certificate is
not such authentication. The native raw-cut CW schema can contain source
self-identifications; no automatic regularization is claimed here.

## Contents

- `article.tex`, `article.pdf`: full proofs, bounds, experiments and twelve further
  research questions; classical ingredients and scope are identified.
- `code/ranked_morse.py`: exact interval preparation, affine/modular rank synthesis,
  independent inequality replay, bounded explicit oracles and serialization.
- `code/sources.py`: modular paths, genuine product cellulations, finite disk-source
  checks and independent explicit geometric comparison.
- `code/demo.py`, `code/verify.py`: binary product demonstration and generic arithmetic
  certificate replay. The generic verifier deliberately returns no ball/knot verdict.
- `tests/test_research.py`: 18 tests, 90,121 counted cases in the retained run.
- `results/`: complete validation, timing records, logs and generated tables.
- `examples/`: small and huge-namespace replayable certificates.
- `INTEGRATION.md`, `SOURCE_AUDIT.md`, `CLAIMS.md`: source, API and claim boundaries.

## Run

Python 3.10+; standard library only. The recorded run used Python 3.13.5.

```sh
python tests/test_research.py
python code/verify.py examples/prism_100bit.json
python code/demo.py --bits 1024
python code/demo.py --bits 16384 --output large_prism.json
python code/benchmark.py
sh build.sh
```

The test runner exits nonzero on failure and writes `results/validation.json`.
Benchmarks write all samples and regenerate the LaTeX tables; their values depend
on the machine. The saved article refers to the retained completed run, so its
narrative numbers may need updating after new measurements. `build.sh` compiles
the article three times and places the PDF at the package root.

## Evidence and scope

The retained 18 tests include 480 independently reconstructed three-dimensional
sources, 444 relative product collapses and 1,000 arbitrary small simplicial
matchings. Signed floor sums, modular constraints, reflected coordinates,
malformed data and cycle rejection are tested separately. Tests on 16,385-bit
namespace bounds disable explicit expansion. The saved proof replays with the
producer and offset solver disabled.

The timing experiment compares the **complete supplied-matching query** from an
already supplied interval packet: structural validation, acyclicity and critical
counts. One arm constructs and replays a compressed rank proof; the other expands
and topologically sorts the graph. Source authentication and serialization are
not timed. Tiny-input regressions and identical-arm controls are retained.
These are not native knot-recognition, AHT or Regina benchmarks. A direct product
argument already recognizes the controlled positive source class; the experiment
isolates the general matching-certificate operation.

## Placement

Reference repository revision:
`704600626606a9097cfd89d4e3d2bbc63c8dd1cb`.
This is a targeted review, not a full checkout; some earlier reads used moving
main. See `SOURCE_AUDIT.md` for the exact scope. Assign the next report number
under `Topology/UnknotRecognition/reports/` during intake. No production patch
is included, no upstream files were changed, and no native test suite was run.
