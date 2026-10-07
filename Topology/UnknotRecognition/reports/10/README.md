# Component compression and restart entropy in exact unknot recognition

Research contribution for `ProveIt/Topology/UnknotRecognition`, 7 October 2026.

The article proves an exact component-quotient factorization for F2
cobordism composition, gives a dense `poly(w) * 2^(w/2)` bit-time composition
algorithm, characterizes its optimal universal information quotient, constructs
explicit planar zipper matching triples, and develops a sharp sparse-profile
restart potential for hierarchy algorithms.

**This is not an unrestricted quasi-polynomial unknot recognizer.** The numerical
kernel is implemented and tested. The sparse hierarchy criterion is conditional
on uniform topological and primitive-cost bounds that are stated, not assumed
proved. No full-recognizer speedup or full repository regression run is claimed.

## Read and reproduce

`article.pdf` is the compiled article. `article.tex` is self-contained and builds
without external figure or bibliography files. The code uses the Python standard
library; this run used Python 3.13.5.

```sh
python tools/run_tests.py
python tools/benchmark.py
make pdf
```

The final recorded validation has **15 test methods, zero failures, zero errors**.
It includes 460,564 matching-composition equalities, 24,000 general-plan
comparisons, 65,980 subset-convolution checks, 1,000 associativity checks, 24
explicit zipper triples, and 23,460 rank/unrank checks. See `results/tests.json`
for exact categories; they are not all independent end-to-end topology tests.

The supplied benchmark is a paired **numerical-kernel microbenchmark**, not a
recognition benchmark. At dense endomorphism sizes k=6,8,10, the recorded paired
median speed ratios are 5.03x, 22.89x, and 86.72x. The 36-endpoint zipper triple
has ratio 401.98x. The forced dense kernel is about 103x slower on the sparse
negative control. The default adapter retains sparse fallback. Tables are
precompiled; compilation time is reported separately. The baseline's numerical
monomial memo is fresh per call. All raw rounds and A/A controls are retained.
These measurements do not predict complete scanner performance or warm-cache
behavior. The small k=4 observed ratio range crosses one.

## Files and integration

`code/component_kernel.py` contains the exact arithmetic and a per-scanner,
opt-in `ComponentAlgebra` wrapper. `code/restart_entropy.py` contains exact sparse
profile counts, ranks, inverse ranks, and a finite-trace checker. The source
excerpt in `tests/reference_planar.py` is explicitly not a complete recognizer.

Read `integration/README.md` before installation. Its local-checkout validation
script is supplied but **was not executed against the full repository here**.
It checks actual source hashes and can compare direct closed-PD scanner runs.
The full Python suite, Rust port, process-race behavior, and complete-input paired
benchmarks still need to be run before default integration. No repository was
modified and no commit or pull request was created.

Suggested destination for this package:
`Topology/UnknotRecognition/research/component-entropy-20261007/`.

`PROVENANCE.json` records audited source blob identifiers and primary references.
`CLAIMS.md` distinguishes proofs, execution evidence, and remaining obligations.
`SHA256SUMS` provides checksums of the distributed files. Third-party paper PDFs
and lecture slides are not redistributed. Code and article are supplied under
MIT-0; the numerical reference excerpt comes from ProveIt's MIT-0 material.

## Main next step

Profile the optional kernel inside the complete scanner, then attack the
constructive low-entropy hierarchy hypothesis: a uniform logarithmic bound on
positive-complexity layers, or another O(log-squared n) profile-entropy bound,
with explicit bit costs for all geometric operations. The article gives eight
research questions and concrete criteria for completing these steps.
