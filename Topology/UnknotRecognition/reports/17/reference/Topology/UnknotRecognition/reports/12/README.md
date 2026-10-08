# Exact cobordism contraction and succinct block cancellation

Research bundle for `ProveIt/Topology/UnknotRecognition`, 7 October 2026.
Suggested location: `Topology/UnknotRecognition/research/frobenius-contraction/`.

## Read first

The article is `docs/article.pdf`; `docs/article.tex` is self-contained. It proves an exact component quotient for compiled cobordisms, an optimality/rank characterization, fast dense contraction, correct nilpotent matrix inversion, and cancellation of tensor-described same-matching blocks without enumerating exponentially many generators.

**This is not a general quasi-polynomial unknot recognizer.** The unconditional quasi-polynomial result is for the explicitly specified structured block problem. A general construction of such blocks from knot diagrams, with controlled size under every transition, remains a research task. The article states the missing hypotheses and gives explicit tensor-rank obstructions.

The adapter is **opt-in**. Dense synthetic compositions improved in the paired measurements, but none of the ordinary diagram benchmarks selected the dense path. Sparse cases can regress. There is no evidence here supporting an unconditional change to the production default.

## Contents

- `src/unknot_frobenius/`: standard-library Python algorithms and algebraic verifier.
- `tests/`: 29 test methods, including extensive exhaustive/seeded comparisons and independent legacy-oracle checks.
- `benchmarks/`, `results/`: reproducible paired experiments, raw JSON/CSV, final test log, and structured-certificate measurements.
- `integration/`: a real-checkout validation script and integration notes.
- `reference/`: provenance-labelled source fixtures. `algebra.py` is byte-identical to its inspected source blob; `planar.py` and `scan_fast.py` are source-derived execution fixtures, not a complete checkout.
- `examples/succinct_interface_2pow40.json`: a verifiable structured algebraic block with 2^40 hidden generators. It does not represent a knot verdict.
- `docs/article.template.tex`, `docs/build_tables.py`: regenerate the self-contained TeX from recorded results.
- `claims.json`: machine-readable scope ledger.

## Reproduce

Python 3.10 or later is required by the type syntax; tested here with CPython 3.13.5. No third-party Python packages are needed.

```sh
python run_tests.py
python benchmarks/run_benchmarks.py --repeats 5
python benchmarks/succinct_example.py
PYTHONPATH=src python -m unknot_frobenius.verify examples/succinct_interface_2pow40.json
sh build.sh
```

The test entrypoint and benchmark scripts set their own import paths and work without `PYTHONPATH`. For the verifier on Windows, set `PYTHONPATH` to the bundle's `src` directory before invoking the module. `build.sh` uses `pdflatex` three times; no BibTeX is needed. Building overwrites only generated TeX/PDF/build logs, not source data. Benchmarks replace their named result files.

## Main interfaces

```python
from unknot_frobenius.kernel import CompiledPlan

# One genus-zero component: two left discs, one right disc, two outputs.
plan = ((0b11, 0b1, 0b11, 0),)
cp = CompiledPlan.from_plan(plan)
answer = cp.apply(f=7, g=3, method="fast")
print(answer, cp.linearized_rank())
```

Packed integer bit number `S` is the coefficient of monomial mask `S`; ordinary integer multiplication is not coefficient-ring multiplication. A plan must partition contiguous input/output variable sets. For current `Planar.compose_plan`, use the first four fields of each component; do not mix the two engines' coefficient numbering. The shipped adapter handles this correctly for composition. The optimized upstream crossing-transfer operation is left unchanged.

```python
from fastunknot.scan_fast import FastScan
from unknot_frobenius.adapters import install_on_empty_scan

scan = FastScan(max_objects=100000)
install_on_empty_scan(scan)  # BEFORE adding any crossing
# Continue using the normal scanner methods.
```

No global monkey patch is used. The adapter rejects nonempty scanner states. Allocation/time exceptions must be handled by the caller as resource limits, never converted into UNKNOT or KNOTTED.

## Theoretical versus production resource limits

Dense transforms and coefficient arrays are exponential in the declared variable count, despite being asymptotically better than the current dense Cartesian loop. The prototype defaults to a limit of 18 variables for selected factored allocations. Mathematical asymptotic bounds refer to the corresponding uncapped algorithmic family with appropriate allocation limits and fast multiplication. Block/tensor experiments here use at most three ring variables. No performance or memory guarantee beyond configured limits is implied.

## Testing scope and next integration step

The full current repository was not downloaded, and its entire test suite was not run. Production-engine tests here use source-derived current fixtures, checked against the independent older set-based engine. To test a real checkout:

```sh
python integration/check_checkout.py --fast-dir /path/to/ProveIt/Topology/UnknotRecognition/fast
```

The script first checks the two inspected production blob hashes. A mismatch requires a fresh audit before using `--allow-version-change`. Then run the checkout's own complete test suite and representative production benchmarks. Do not attribute the source-fixture results to a full-checkout run.

## Licensing and attribution

New code and article source are distributed under MIT-0 for repository integration. Retained upstream/oracle fixtures preserve their original MIT-0 notice in `reference/legacy/LICENSE`. The subset-convolution algorithm is credited to Björklund, Husfeldt, Kaski, and Koivisto; the general Schur, inverse, and tensor identities are not claimed as new inventions. No third-party research PDFs or font files are bundled.
