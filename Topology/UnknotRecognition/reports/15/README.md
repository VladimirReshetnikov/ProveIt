# Sharp radical bounds and survivor-first compression

Research package for `ProveIt/Topology/UnknotRecognition`, 7 October 2026.

Read **article/article.pdf** for the proofs, precise complexity hypotheses,
benchmarks, and eleven further research questions. The package does **not**
claim an unrestricted quasi-polynomial unknot recognizer or a measured speedup
against the optimized upstream `FastScan`.

## Main results

For the characteristic-two arc category with 2k boundary points:

* The radical has sharp nilpotence index 2k, for k >= 1.
* A marked dot splits the algebra as B tensor F2[z]/(z^2); B has radical
  index 2k-1, and this gives a two-pass transfer formula.
* Binary residue homology predicts the exact minimal multiplicity of each
  matching in each homological degree. Pivot order cannot change this profile.
* A finite homological perturbation computes the differential on those survivors.
  Correction order 2k-2 is necessary in general; explicit witnesses are included.
* The parameterized scan bound is polynomial(input size) times
  2^O(boundary half-width) times the cube of the largest minimal survivor count.
  A uniform quasi-polynomial conclusion still needs the structural hypotheses
  stated in the paper.

The classical arc category, minimal-model machinery, and perturbation lemma
are credited in the article. First-in-literature novelty is not asserted.

## Reproduce

Python 3.10+ and the standard library are sufficient for the mathematical code.
The recorded run used CPython 3.13.5. Building the paper additionally needs
pdfLaTeX and the standard packages named in its source.

```sh
./reproduce.sh
# Or individual commands:
python -m unittest discover -s tests -v
python experiments/validate_algebra.py
python experiments/validate_braids.py
python experiments/validate_marked.py
python experiments/benchmark.py
python experiments/make_tables.py
make paper
```

The test/validation outputs and all five repetitions of each benchmark are in
`results/`. Reruns overwrite the corresponding results, regenerate numerical
LaTeX tables, and naturally produce different timing values. The article's
mathematical claims are independent of those timings. `SHA256SUMS` describes
the delivered snapshot, not a subsequent local rerun.

## Minimal example

```python
import sys
sys.path.insert(0, 'code')
from braid_scan import scan_braid

result = scan_braid(3, [1, -2, 1, -2], certificate=True)
assert result['unreduced_rank'] == 10
print(result['trace'])
```

This computes the unreduced F2 Khovanov rank of the braid closure. The harness
returns ranks, not a production recognition verdict. A knot decision additionally
requires a verified one-component input. The default transfer function validates
the supplied differential; `validate=False` is appropriate only for an input
known valid from its construction or checked separately. Full certificates are
more expensive than constructing the minimal differential alone.

## Actual completed checks

18 unit-test methods; 2,244 exhaustive monomial composition/derivation checks;
500 random full transfer certificates; 500 minimal-profile comparisons; sharp
radical words through k=12; sharp transfer examples through k=8; 308 marked
transfer certificates; 306 braid closures against an independently assembled
crossing cube; and 1,365 full intermediate braid-stage certificates.

The adapter has a mock-interface test, **not** an upstream checkout test.
The full upstream Python/Rust suite was not run. The two-pass implementation
retains full coefficient encodings and is not claimed to save memory or time.

## Files and deployment

`code/radical.py` contains the exact core. `code/braid_scan.py` is the local
research harness. `vendor/` contains two attributed validation excerpts from
prior project artifacts. `integration/` contains a non-mutating profile adapter
for the reviewed reference `ScanComplex` interface, deployment notes, and
explicit warnings about the different optimized `FastScan` layout.

Suggested integration destination:
`Topology/UnknotRecognition/research/radical_transfer/`.
No repository or persistent Library files were changed by preparing this archive.

See `CLAIMS.md`, `REVIEW_CHECKLIST.md`, and `PROVENANCE.json` before integration.
